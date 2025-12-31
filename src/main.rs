use alang::parse_program;

fn main() {
    // Example alang program
    let source = r#"
        ; Type declaration
        (type Point (struct [x Int] [y Int]))

        ; Function definition
        (def distance [p1 p2] -> Float
          (let [dx (- (. p1 x) (. p2 x))]
               [dy (- (. p1 y) (. p2 y))]
            (sqrt (+ (* dx dx) (* dy dy)))))

        ; Sum type
        (type Option [a] (| (Some a) None))

        ; Generic function
        (def map [f list] -> (List b)
          (match list
            ((Cons head tail) (Cons (f head) (map f tail)))
            (Nil Nil)))
    "#;

    match parse_program(source) {
        Ok(program) => {
            println!("Successfully parsed {} declarations:", program.decls.len());
            for (i, decl) in program.decls.iter().enumerate() {
                match decl {
                    alang::Decl::Type { name, params, .. } => {
                        if params.is_empty() {
                            println!("  {}. Type: {}", i + 1, name);
                        } else {
                            println!("  {}. Type: {}[{}]", i + 1, name, params.join(", "));
                        }
                    }
                    alang::Decl::Def {
                        name, type_params, ..
                    } => {
                        if type_params.is_empty() {
                            println!("  {}. Function: {}", i + 1, name);
                        } else {
                            println!(
                                "  {}. Function: {}[{}]",
                                i + 1,
                                name,
                                type_params.join(", ")
                            );
                        }
                    }
                }
            }
            println!("\nParse successful!");
        }
        Err(error) => {
            eprint!("{}", error);
            std::process::exit(1);
        }
    }
}
