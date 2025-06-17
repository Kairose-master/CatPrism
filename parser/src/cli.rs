use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "catprism")]
#[command(author = "Jinwoo Jang <jinwoo@example.com>")]
#[command(version = "0.1.0")]
#[command(about = "CatPrism DSL toolchain CLI", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Parse .cat file and emit JSON AST
    Parse {
        /// Input .cat file path
        #[arg(short, long)]
        input: String,

        /// Output JSON file path
        #[arg(short, long)]
        output: Option<String>,
    },

    /// Convert .cat file into Lean proof script
    ExportLean {
        /// Input .cat file
        #[arg(short, long)]
        input: String,

        /// Output .lean file directory
        #[arg(short, long)]
        out: Option<String>,
    },
}

