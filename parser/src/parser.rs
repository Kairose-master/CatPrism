use std::fs;
use crate::ast::*;
use serde_json;

/// Parse a `.cat` file and return the CatPrismAST
pub fn parse_cat_file(path: &str) -> CatPrismAST {
    let content = fs::read_to_string(path).expect("Cannot read .cat file");

    // Very simple ad-hoc line-based parser
    let mut categories = Vec::new();
    let mut metric = Metric {
        name: String::from(""),
        lambda: String::from(""),
    };
    let mut functor = FunctorMap {
        name: String::from(""),
        from: String::from(""),
        to: String::from(""),
        object_map: std::collections::HashMap::new(),
        morphism_map: std::collections::HashMap::new(),
        epsilon: 0.0,
        rule: String::from(""),
    };

    let mut current_cat: Option<Category> = None;

    for line in content.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("category") {
            if let Some(cat) = current_cat.take() {
                categories.push(cat);
            }
            let name = trimmed.split_whitespace().nth(1).unwrap().to_string();
            current_cat = Some(Category {
                name,
                objects: Vec::new(),
                morphisms: Vec::new(),
            });
        } else if trimmed.starts_with("object ") {
            if let Some(cat) = current_cat.as_mut() {
                let obj = trimmed.split_whitespace().nth(1).unwrap().to_string();
                cat.objects.push(obj);
            }
        } else if trimmed.starts_with("morphism") {
            if let Some(cat) = current_cat.as_mut() {
                let parts: Vec<&str> = trimmed.split(':').collect();
                let name = parts[0]
                    .split_whitespace()
                    .nth(1)
                    .unwrap()
                    .trim()
                    .to_string();
                let arrow_parts: Vec<&str> = parts[1].split("->").map(|s| s.trim()).collect();
                if arrow_parts.len() == 2 {
                    let from = arrow_parts[0];
                    let to = arrow_parts[1];
                    cat.morphisms.push(Morphism {
                        name,
                        from: from.to_string(),
                        to: to.to_string(),
                    });
                }
            }
        } else if trimmed.starts_with("metric") {
            let name = trimmed.split_whitespace().nth(1).unwrap().to_string();
            metric.name = name;
        } else if trimmed.contains("lambda") {
            let lambda = trimmed.split("=>").nth(1).unwrap().trim().to_string();
            metric.lambda = lambda;
        } else if trimmed.starts_with("functor") {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            functor.name = parts[1].to_string();
            functor.from = parts[3].to_string();
            functor.to = parts[5].to_string();
        } else if trimmed.starts_with("object_map") || trimmed.starts_with("object_map {") {
            continue;
        } else if trimmed.contains("->") && trimmed.contains(',') == false {
            let parts: Vec<&str> = trimmed.split("->").map(|s| s.trim()).collect();
            if parts.len() == 2 {
                if trimmed.contains("object") || trimmed.contains("}") {
                    continue;
                }
                functor.object_map.insert(parts[0].to_string(), parts[1].to_string());
            }
        } else if trimmed.contains("epsilon") {
            let eps = trimmed.split(':').nth(1).unwrap().trim().parse::<f64>().unwrap();
            functor.epsilon = eps;
        } else if trimmed.contains("distortion_metric") {
            // ignore: already in metric
        } else if trimmed.contains("rule") {
            functor.rule = trimmed.split(':').nth(1).unwrap().trim().to_string();
        }
    }

    if let Some(cat) = current_cat {
        categories.push(cat);
    }

    CatPrismAST {
        categories,
        metric,
        functor,
    }
}

