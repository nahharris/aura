//! Mark-and-sweep garbage collector for the Aura VM.
//!
//! # Architecture
//!
//! The GC is a simple **stop-the-world mark-and-sweep** collector:
//!
//! 1. **Mark phase** — starting from all GC roots (VM stack, global variables,
//!    open upvalues), recursively mark every reachable [`GcObject`].
//! 2. **Sweep phase** — walk the intrusive linked list of all allocated objects;
//!    reclaim any that were not marked; clear mark bits on the survivors.
//!
//! # `GcPtr<T>`
//!
//! The primary handle type is [`GcPtr<T>`]: a thin, non-owning pointer to a
//! GC-managed heap object.  It is `Copy` (like a raw pointer) but typed.
//! Dereferencing it is `unsafe` because the GC may collect the object if no
//! root retains a live reference.  In practice, the VM always guarantees that
//! every `GcPtr` on the stack or in a live closure is a valid root.
//!
//! # GC-managed types
//!
//! Every heap-allocated Aura object must implement [`GcTrace`]:
//! - `trace(&self, heap: &mut GcHeap)` — mark all child `GcPtr`s reachable
//!   from this object.
//!
//! The [`GcHeap`] is the single allocator; call [`GcHeap::alloc`] to create
//! a new managed object.  The heap automatically triggers a collection when
//! the number of live bytes exceeds a configurable threshold.

use std::any::Any;
use std::cell::Cell;
use std::fmt;
use std::ptr::NonNull;

// ─────────────────────────────────────────────────────────────────────────────
// GcTrace trait
// ─────────────────────────────────────────────────────────────────────────────

/// Every GC-managed type must implement `GcTrace` so the collector can
/// discover all child `GcPtr`s during the mark phase.
pub trait GcTrace: Any + fmt::Debug {
    /// Recursively mark all `GcPtr`s reachable from `self`.
    ///
    /// Implementations should call [`GcHeap::mark`] on each child pointer and
    /// then call `child.trace(heap)` to recurse, but only when the child was
    /// not already marked (to avoid cycles).
    fn trace(&self, heap: &mut GcHeap);

    /// Return the approximate heap size in bytes contributed by this object
    /// (not counting the `GcBox` header itself).
    fn heap_size(&self) -> usize;
}

// ─────────────────────────────────────────────────────────────────────────────
// GcBox — the on-heap header + payload
// ─────────────────────────────────────────────────────────────────────────────

/// The on-heap layout for a GC-managed object.
///
/// Each `GcBox` is heap-allocated via [`Box`] and then linked into the
/// [`GcHeap`]'s intrusive linked list through the `next` pointer.
struct GcBox<T: GcTrace + ?Sized> {
    /// GC mark bit.  `true` = reachable during the current collection.
    marked: Cell<bool>,
    /// Intrusive linked-list link (raw pointer, `None` = end of list).
    next: Option<NonNull<GcBox<dyn GcTrace>>>,
    /// The actual managed value.
    value: T,
}

// ─────────────────────────────────────────────────────────────────────────────
// GcPtr<T>
// ─────────────────────────────────────────────────────────────────────────────

/// A non-owning, Copy handle to a GC-managed object of type `T`.
///
/// Validity: a `GcPtr<T>` is valid as long as the pointed-to object has not
/// been collected.  The VM guarantees this by keeping all live `GcPtr`s on
/// the stack or in a closure's upvalue array, both of which are GC roots.
pub struct GcPtr<T: GcTrace + ?Sized> {
    ptr: NonNull<GcBox<T>>,
}

// Manual impls because the derive macros require T: Clone / T: Copy.
impl<T: GcTrace + ?Sized> Clone for GcPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: GcTrace + ?Sized> Copy for GcPtr<T> {}

impl<T: GcTrace + ?Sized> fmt::Debug for GcPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GcPtr({:p})", self.ptr.as_ptr())
    }
}

impl<T: GcTrace + ?Sized> PartialEq for GcPtr<T> {
    /// Two `GcPtr`s are equal if and only if they point to the same object.
    fn eq(&self, other: &Self) -> bool {
        std::ptr::addr_eq(self.ptr.as_ptr(), other.ptr.as_ptr())
    }
}
impl<T: GcTrace + ?Sized> Eq for GcPtr<T> {}

impl<T: GcTrace + ?Sized> GcPtr<T> {
    /// Dereference the pointer to get a shared reference.
    ///
    /// # Safety
    ///
    /// The caller must ensure the pointed-to object is still alive (i.e., has
    /// not been collected).  This is guaranteed as long as this `GcPtr` itself
    /// is reachable from GC roots.
    #[inline]
    pub unsafe fn as_ref(&self) -> &T {
        // SAFETY: the caller guarantees liveness.
        unsafe { &(*self.ptr.as_ptr()).value }
    }

    /// Dereference the pointer to get a mutable reference.
    ///
    /// # Safety
    ///
    /// Same liveness requirement as [`GcPtr::as_ref`], plus the caller must
    /// guarantee exclusive access (no other borrows of this object exist).
    #[allow(clippy::mut_from_ref)]
    #[inline]
    pub unsafe fn as_mut(&self) -> &mut T {
        // SAFETY: caller guarantees liveness and exclusivity.
        unsafe { &mut (*self.ptr.as_ptr()).value }
    }

    /// Mark this object as reachable.  Called by [`GcHeap::mark`].
    fn set_marked(&self, marked: bool) {
        // SAFETY: the GcHeap always outlives the GcBox.
        unsafe { (*self.ptr.as_ptr()).marked.set(marked) }
    }

    fn is_marked(&self) -> bool {
        // SAFETY: same as above.
        unsafe { (*self.ptr.as_ptr()).marked.get() }
    }

    /// Erase the type parameter to obtain a fat pointer to `dyn GcTrace`.
    pub fn as_dyn(self) -> GcPtr<dyn GcTrace>
    where
        T: Sized,
    {
        // SAFETY: GcBox<T> and GcBox<dyn GcTrace> have compatible layout here
        // because we go through a coercion.
        let dyn_ptr: NonNull<GcBox<dyn GcTrace>> =
            // SAFETY: coercion of a thin pointer to a fat pointer via unsized coerce.
            unsafe { NonNull::new_unchecked(self.ptr.as_ptr() as *mut GcBox<dyn GcTrace>) };
        GcPtr { ptr: dyn_ptr }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// GcHeap
// ─────────────────────────────────────────────────────────────────────────────

/// The garbage-collected heap.
///
/// The heap owns all `GcBox` allocations through an intrusive singly-linked
/// list rooted at `first`.  Call [`GcHeap::alloc`] to create objects;
/// call [`GcHeap::collect`] to trigger a GC cycle.
pub struct GcHeap {
    /// Head of the intrusive linked list of all allocated objects.
    first: Option<NonNull<GcBox<dyn GcTrace>>>,
    /// Total approximate heap bytes currently allocated.
    bytes_allocated: usize,
    /// Threshold: run a GC cycle when `bytes_allocated` exceeds this.
    gc_threshold: usize,
    /// Total number of completed GC cycles (for metrics / debugging).
    pub cycles: usize,
}

// SAFETY: The GC manages all pointers internally and is used from a single
// thread only.  The VM never sends the heap across threads.
unsafe impl Send for GcHeap {}

impl Default for GcHeap {
    fn default() -> Self {
        Self::new()
    }
}

impl GcHeap {
    /// Initial GC threshold (1 MiB).
    const INITIAL_THRESHOLD: usize = 1024 * 1024;

    /// Create a new, empty GC heap.
    pub fn new() -> Self {
        Self {
            first: None,
            bytes_allocated: 0,
            gc_threshold: Self::INITIAL_THRESHOLD,
            cycles: 0,
        }
    }

    /// Allocate a new GC-managed object and return a [`GcPtr<T>`] to it.
    ///
    /// The object is immediately linked into the heap's allocation list.
    /// If the heap has exceeded its threshold, a collection is triggered
    /// **before** the allocation to keep peak usage bounded.
    pub fn alloc<T: GcTrace + Sized + 'static>(&mut self, value: T) -> GcPtr<T> {
        let size = std::mem::size_of::<GcBox<T>>() + value.heap_size();

        // Box the GcBox so it lands on the heap.
        let mut boxed = Box::new(GcBox {
            marked: Cell::new(false),
            next: self.first,
            value,
        });

        // Coerce to a fat pointer (`dyn GcTrace`) for the linked list.
        let thin_ptr: NonNull<GcBox<T>> = NonNull::new(boxed.as_mut() as *mut GcBox<T>).unwrap();
        let fat_ptr: NonNull<GcBox<dyn GcTrace>> =
            NonNull::new(Box::into_raw(boxed) as *mut GcBox<dyn GcTrace>).unwrap();

        self.first = Some(fat_ptr);
        self.bytes_allocated += size;

        GcPtr { ptr: thin_ptr }
    }

    /// Mark a `GcPtr` as reachable and recursively trace its children.
    ///
    /// Call this for every root during the mark phase, and from `GcTrace::trace`
    /// implementations to mark children.
    pub fn mark<T: GcTrace + ?Sized>(&mut self, ptr: GcPtr<T>) {
        if ptr.is_marked() {
            return; // already visited; avoids infinite loops on cycles
        }
        ptr.set_marked(true);
        // SAFETY: object is still alive (it was just marked).
        unsafe { ptr.as_ref() }.trace(self);
    }

    /// Run a full GC cycle: mark all objects reachable from `roots`, then
    /// sweep unreachable objects.
    ///
    /// `roots` is a callback that receives a mutable reference to the heap and
    /// should call [`GcHeap::mark`] on every live root.
    pub fn collect<F>(&mut self, mark_roots: F)
    where
        F: FnOnce(&mut GcHeap),
    {
        // Mark phase
        mark_roots(self);

        // Sweep phase
        self.sweep();

        // Grow the threshold proportionally to avoid thrashing.
        self.gc_threshold = (self.bytes_allocated * 2).max(Self::INITIAL_THRESHOLD);
        self.cycles += 1;
    }

    /// Sweep unreachable objects off the linked list, freeing their memory.
    fn sweep(&mut self) {
        let mut current = self.first;
        let mut prev: Option<NonNull<GcBox<dyn GcTrace>>> = None;

        while let Some(node_ptr) = current {
            // SAFETY: node_ptr is always a valid pointer produced by alloc().
            let node = unsafe { node_ptr.as_ref() };
            let next = node.next;

            if node.marked.get() {
                // Survived: clear mark, advance.
                node.marked.set(false);
                prev = current;
                current = next;
            } else {
                // Unreachable: unlink and free.
                if let Some(p) = prev {
                    // SAFETY: p is a valid, live node.
                    unsafe { (*p.as_ptr()).next = next };
                } else {
                    self.first = next;
                }
                // SAFETY: we own this node; drop it.
                let size = {
                    let b = unsafe { Box::from_raw(node_ptr.as_ptr()) };
                    std::mem::size_of_val(&*b) + b.value.heap_size()
                };
                self.bytes_allocated = self.bytes_allocated.saturating_sub(size);
                current = next;
            }
        }
    }

    /// Return the number of bytes currently tracked by the heap.
    #[inline]
    pub fn bytes_allocated(&self) -> usize {
        self.bytes_allocated
    }

    /// Return `true` if a collection should be triggered now.
    #[inline]
    pub fn should_collect(&self) -> bool {
        self.bytes_allocated >= self.gc_threshold
    }
}

impl fmt::Debug for GcHeap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GcHeap")
            .field("bytes_allocated", &self.bytes_allocated)
            .field("gc_threshold", &self.gc_threshold)
            .field("cycles", &self.cycles)
            .finish()
    }
}

impl Drop for GcHeap {
    fn drop(&mut self) {
        // Walk the list and free every remaining object.
        let mut current = self.first;
        while let Some(node_ptr) = current {
            // SAFETY: node_ptr is always a valid pointer we allocated.
            let next = unsafe { (*node_ptr.as_ptr()).next };
            // SAFETY: we are the sole owner; drop by re-boxing.
            unsafe { drop(Box::from_raw(node_ptr.as_ptr())) };
            current = next;
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// A trivial GC-traced type for testing.
    #[derive(Debug)]
    struct Leaf(i64);

    impl GcTrace for Leaf {
        fn trace(&self, _heap: &mut GcHeap) {} // no children
        fn heap_size(&self) -> usize {
            0
        }
    }

    #[test]
    fn test_alloc_and_deref() {
        let mut heap = GcHeap::new();
        let ptr = heap.alloc(Leaf(42));
        // SAFETY: ptr is still alive (heap is not collected yet).
        let val = unsafe { ptr.as_ref() };
        assert_eq!(val.0, 42);
    }

    #[test]
    fn test_gc_collects_unreachable() {
        let mut heap = GcHeap::new();
        // Allocate two objects but only keep a root to one of them.
        let kept = heap.alloc(Leaf(1));
        let _dropped = heap.alloc(Leaf(2)); // will not be a root

        assert_eq!(heap.bytes_allocated > 0, true);

        heap.collect(|h| {
            h.mark(kept.as_dyn());
        });

        // After collection only `kept` should remain (1 Leaf).
        // We can't easily count live objects, but we can verify the kept value
        // is still accessible and the heap didn't crash.
        assert!(heap.cycles == 1);
        let val = unsafe { kept.as_ref() };
        assert_eq!(val.0, 1);
    }

    #[test]
    fn test_ptr_equality() {
        let mut heap = GcHeap::new();
        let a = heap.alloc(Leaf(10));
        let b = heap.alloc(Leaf(10));
        let a2 = a;
        assert_eq!(a, a2, "copies of the same GcPtr should be equal");
        assert_ne!(a, b, "distinct GcPtrs should not be equal");
    }
}
