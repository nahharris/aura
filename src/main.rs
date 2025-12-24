use aura::parser::parse;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Aura Grammar & Parser Verification");
    println!("----------------------------------");

    let examples = vec![
        ("Assignment", "x = 1;"),
        ("Let Binding", "let x = 1;"),
        ("Const Binding", "const y = 2;"),
        ("List", "[1, 2, 3]"),
        ("List with Block", "[ let x = 0; x = x + 1; x, 2 ]"),
        ("Tuple", "(1, 2)"),
        ("Function", "fn add(a: Int, b: Int) -> Int { a + b }"),
        ("If Macro", r#"
            if (x > 0) {
                print("positive");
            } else {
                print("negative");
            }
        "#),
        ("While Macro", r#"
            while (x > 0) do {
                x = x - 1;
            }
        "#),
        ("Loop Macro", r#"
            loop {
                print("Hello");
            }
        "#),
        ("Complex Call", r#"
            do(1) { x -> 
                print(x); 
            } that { y -> 
                print(y); 
            }
        "#),
        ("Method Call", "x.toString()"),
        ("Enum Variant", ".ok(1)"),
        ("Safe Nav", "x?.y"),
    ];

    for (name, code) in examples {
        println!("\nTesting: {}", name);
        match parse(code) {
            Ok(ast) => println!("Success: {:#?}", ast),
            Err(e) => println!("Error: {}", e),
        }
    }

    Ok(())
}
