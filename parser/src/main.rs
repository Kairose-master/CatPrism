use clap::Parser;

mod ast;
mod cli;
mod export;
mod parser;

use cli::{Cli, Commands};
use parser::parse_cat_file;
use export::export_to_lean;

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Parse { input, output } => {
            let ast = parse_cat_file(&input);
            let json = serde_json::to_string_pretty(&ast).expect("failed to serialize AST");
            if let Some(out_path) = output {
                std::fs::write(out_path, json).expect("failed to write JSON output");
            } else {
                println!("{}", json);
            }
        }
        Commands::ExportLean { input, out } => {
            let ast = parse_cat_file(&input);
            let out_dir = out.unwrap_or_else(|| ".".to_string());
            let file_stem = std::path::Path::new(&input)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("output")
                .to_string();
            export_to_lean(&ast, &out_dir, &file_stem);
        }
    }
}
