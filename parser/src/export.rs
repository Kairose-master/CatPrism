use std::fs;
use crate::ast::CatPrismAST;
use std::path::Path;

/// Convert AST into Lean code using the new, refactored template structure.
/// This function now generates separate proof blocks for composition and identity laws.
pub fn export_to_lean(ast: &CatPrismAST, out_dir: &str, filename: &str) {
    // It's crucial that this template file is updated to match the new EpsFunctor structure.
    let template = include_str!("../templates/functor.lean");

    // Generate object mappings for the `match` block.
    // The indentation is important for correct Lean formatting.
    let object_map = ast.functor.object_map.iter()
        .map(|(src, tgt)| format!("      | {}.{} => {}.{}", ast.functor.from, src, ast.functor.to, tgt))
        .collect::<Vec<_>>()
        .join("\n");

    // Generate morphism mappings for the `match` block.
    let morphism_map = ast.functor.morphism_map.iter()
        .map(|(src, tgt)| format!("      | {}.{} => {}.{}", ast.functor.from, src, ast.functor.to, tgt))
        .collect::<Vec<_>>()
        .join("\n");

    // Generate a unique namespace for the proof.
    let namespace = format!("{}Proof", ast.functor.name);
    // Generate the functor definition name.
    let functor_name = format!("F_{}", ast.functor.name.to_lowercase());

    // ✍️ ** 주요 변경 사항: **
    // `comp_ok`와 `id_ok`에 대한 증명 택틱을 별도로 생성합니다.
    // 이는 새로운 Lean 템플릿의 `{proof_block_comp}`와 `{proof_block_id}`에 대응됩니다.
    let (proof_block_comp, proof_block_id) = match ast.functor.rule.as_str() {
        "preserve_composition_within ε" => ("    verify_comp".to_string(), "    verify_id".to_string()),
        _ => ("    sorry".to_string(), "    sorry".to_string()),
    };

    // Replace all placeholders in the template with the generated content.
    let content = template
        .replace("{source_file}", filename)
        .replace("{metric}", &ast.metric.name)
        .replace("{epsilon}", &ast.functor.epsilon.to_string())
        .replace("{object_map}", &object_map)
        .replace("{morphism_map}", &morphism_map)
        .replace("{namespace}", &namespace)
        .replace("{functor_name}", &functor_name)
        .replace("{proof_block_comp}", &proof_block_comp)
        .replace("{proof_block_id}", &proof_block_id);

    // Ensure the output directory exists before writing the file.
    if let Err(e) = fs::create_dir_all(out_dir) {
        eprintln!("Error: Failed to create output directory {}: {}", out_dir, e);
        return;
    }

    // Write the final content to the .lean file.
    let out_path = Path::new(out_dir).join(format!("{}.lean", ast.functor.name));
    if let Err(e) = fs::write(&out_path, &content) {
        eprintln!("Error: Failed to write lean file to {:?}: {}", out_path, e);
    } else {
        println!("Successfully generated Lean file at {:?}", out_path);
    }
}


