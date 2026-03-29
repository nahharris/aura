use super::*;

pub(super) fn register(vm: &mut Vm) {
    vm.register_native("net_tcp_connect", net_tcp_connect);
    vm.register_native("net_tcp_listen", net_tcp_listen);
    vm.register_native("net_tcp_accept", net_tcp_accept);
    vm.register_native("net_tcp_send", net_tcp_send);
    vm.register_native("net_tcp_recv", net_tcp_recv);
    vm.register_native("net_tcp_close", net_tcp_close);
    vm.register_native("net_udp_bind", net_udp_bind);
    vm.register_native("net_udp_send_to", net_udp_send_to);
    vm.register_native("net_udp_recv_from", net_udp_recv_from);
    vm.register_native("net_udp_close", net_udp_close);
    vm.register_native("net_http_get", net_http_get);
    vm.register_native("net_http_post", net_http_post);
}
