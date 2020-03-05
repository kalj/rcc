extern crate clap;
use clap::{App, Arg};
use std::fs;
use std::path::{Path, PathBuf};

mod tokenizer;
use tokenizer::tokenize;

mod parser;
use parser::{parse, print_program};

mod codegen;
use codegen::Generator;

fn print_error_message(source: &str, source_path: &Path, cursor: usize, msg: &str) {
    let mut line_starts = Vec::new();
    line_starts.push(0 as usize);

    for m in source.match_indices('\n') {
        let (idx,_) = m;
        line_starts.push(idx + 1);
    }

    line_starts.push(source.len()); // put the end of file last

    let row = line_starts.iter().rposition(|ls| ls <= &cursor).unwrap();
    let col = cursor - line_starts[row];
    let rowstart = line_starts[row];
    let rowend = line_starts[row + 1];

    println!("{}:{}:{}:{}", source_path.display(), row, col, msg);
    println!("{}", &source[rowstart..rowend]);
    println!("{:<1$}^", "", col);
}

fn main() {
    let matches = App::new("c-compiler")
        .arg(Arg::with_name("INPUT").help("The source file to compile").required(true))
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .value_name("OUTPUT")
                .help("The output assembly file (INPUT with suffix .s by default)"),
        )
        .arg(
            Arg::with_name("BITS")
                .short("m")
                .possible_values(&["64", "32"])
                .default_value("64")
                .help("Specify 32 or 64 bit code generation."),
        )
        .arg(Arg::with_name("verbose").short("v").long("verbose").help("Enable verbose output"))
        .get_matches();

    let source_filename = matches.value_of("INPUT").unwrap();
    let source_path = Path::new(source_filename);

    let emit_32bit = matches.value_of("BITS").unwrap() == "32";
    let verbose = matches.is_present("verbose");

    match source_path.extension() {
        Some(x) if x.to_str() == Some("c") => (),
        _ => {
            println!("Expected c source file with extension .c");
            std::process::exit(1)
        }
    }

    let output_path: PathBuf = match matches.value_of("OUTPUT") {
        Some(p) => PathBuf::from(p),
        None => source_path.with_extension("s"),
    };

    if verbose {
        println!("Compiling {} -> {}...", source_path.display(), output_path.display());
    }

    let source = fs::read_to_string(source_path).expect("Failed reading source file");

    if verbose {
        println!("Got source:");
        println!("{}", source);
    }

    let tokens = match tokenize(&source) {
        Ok(t) => t,
        Err(err) => {
            print_error_message(&source, source_path, err.cursor, "Unknown token");
            std::process::exit(1);
        }
    };


    if verbose {
        println!("After tokenization:");
        let tokenstrs: Vec<String> = tokens.iter().map(|t| format!("{}", t.token)).collect();
        println!("{}", tokenstrs.join(" "));
    }

    let program = match parse(&tokens) {
        Ok(prog) => prog,
        Err(err) => {
            let error_message = format!("ParseError: {}", err.message);
            print_error_message(&source, &source_path, err.cursor, &error_message);
            std::process::exit(1);
        }
    };

    if verbose {
        println!("After parsing:");
        print_program(&program);
    }

    let mut generator = Generator::new(emit_32bit);
    let assembly_code = generator.generate_program_code(program);

    fs::write(output_path, assembly_code.get_str()).expect("Failed writing assembly output");
}
