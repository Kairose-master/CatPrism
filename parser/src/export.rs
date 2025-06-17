use std::fs;
use std::collections::HashMap;
use crate::ast::{CatPrismAST, Category, Morphism, FunctorMap, Metric};
use std::path::Path;

/// Convert AST into Lean code using embedded template
pub fn export_to_lean(ast: &CatPrismAST, out_dir: &str, filename: &str) {
    let template = include_str!("../templates/functor.lean");

    let object_map = ast.functor.object_map.iter()
        .map(|(src, tgt)| format!("      | {}.{} => {}.{}", ast.functor.from, src, ast.functor.to, tgt))
        .collect::<Vec<_>>()
        .join("\n");

    let morphism_map = ast.functor.morphism_map.iter()
        .map(|(src, tgt)| format!("      | {}.{} => {}.{}", ast.functor.from, src, ast.functor.to, tgt))
        .collect::<Vec<_>>()
        .join("\n");

    let namespace = format!("{}Proof", ast.functor.name);
    let functor_name = format!("F_{}", ast.functor.name.to_lowercase());

    let proof_block = match ast.functor.rule.as_str() {
        "preserve_composition_within ε" => "    verify_comp".to_string(),
        _ => "    sorry".to_string(),
    };

    let content = template
        .replace("{source_file}", filename)
        .replace("{metric}", &ast.metric.name)
        .replace("{epsilon}", &ast.functor.epsilon.to_string())
        .replace("{object_map}", &object_map)
        .replace("{morphism_map}", &morphism_map)
        .replace("{namespace}", &namespace)
        .replace("{functor_name}", &functor_name)
        .replace("{proof_block}", &proof_block);

    let out_path = Path::new(out_dir).join(format!("{}.lean", ast.functor.name));
    fs::write(out_path, content).expect("failed to write lean file");
}

