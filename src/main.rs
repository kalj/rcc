extern crate clap;

mod ast;
mod codegen;
mod evaluation;
mod parser;
mod symbol_table;
mod tokenizer;
mod validation;

use ast::print_program;
use clap::{
  App,
  Arg,
};
use codegen::generate_code;
use parser::parse;
use std::{
  fs,
  path::{
    Path,
    PathBuf,
  },
};
use tokenizer::tokenize;
use validation::validate;

fn print_error_message(source: &str, source_path: &Path, position: usize, length: usize, msg: &str) {
  let mut line_starts = vec![0_usize];

  for m in source.match_indices('\n') {
    let (idx, _) = m;
    line_starts.push(idx + 1);
  }

  line_starts.push(source.len()); // put the end of file last

  let row = line_starts.iter().rposition(|ls| ls <= &position).unwrap();
  let col = position - line_starts[row];
  let rowstart = line_starts[row];
  let rowend = line_starts[row + 1];

  println!("{}:{}:{}:{}", source_path.display(), row, col, msg);
  println!("{}", source[rowstart..rowend].trim_end());
  println!("{:<1$}{2}", "", col, "^".repeat(length));
}

fn main() {
  let matches = App::new("c-compiler")
    .arg(Arg::with_name("INPUT").help("The source file to compile").required(true))
    .arg(
      Arg::with_name("OUTPUT")
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
    },
  }

  let output_path: Option<PathBuf> = match matches.value_of("OUTPUT") {
    Some(p) => {
      if p == "-" {
        None
      } else {
        Some(PathBuf::from(p))
      }
    },
    None => Some(source_path.with_extension("s")),
  };

  let source = fs::read_to_string(source_path).expect("Failed reading source file");

  if verbose {
    println!("Got source:");
    println!("{}", source);
  }

  let tokens = match tokenize(&source) {
    Ok(t) => t,
    Err(err) => {
      print_error_message(&source, source_path, err.cursor, 1, "Unknown token");
      std::process::exit(1);
    },
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
      print_error_message(&source, &source_path, err.position, err.length, &error_message);
      std::process::exit(1);
    },
  };

  if verbose {
    println!("After parsing:");
    print_program(&program);
  }

  let validation_errors = validate(&program);
  if !validation_errors.is_empty() {
    for err in validation_errors {
      let error_message = format!("ValidationError: {}", err.message);
      print_error_message(&source, &source_path, err.position, err.length, &error_message);
    }
    std::process::exit(1);
  }

  let code = match generate_code(&program, emit_32bit) {
    Ok(prog) => prog,
    Err(err) => {
      let error_message = format!("CodegenError: {}", err.message);
      print_error_message(&source, &source_path, err.position, err.length, &error_message);
      std::process::exit(1);
    },
  };

  if let Some(path) = output_path {
    if verbose {
      println!("Writing assembly output to {}", path.display());
    }

    fs::write(path, code.get_str()).expect("Failed writing assembly output");
  } else {
    if verbose {
      println!("Writing assembly output to stdout");
    }
    print!("{}", code.get_str());
  }
}
