use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Category {
    pub name: String,
    pub objects: Vec<String>,
    pub morphisms: Vec<Morphism>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Morphism {
    pub name: String,
    pub from: String,
    pub to: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Metric {
    pub name: String,
    pub lambda: String,  // representation of distance function
}

#[derive(Debug, Serialize, Deserialize)]
pub struct FunctorMap {
    pub name: String,
    pub from: String,
    pub to: String,
    pub object_map: std::collections::HashMap<String, String>,
    pub morphism_map: std::collections::HashMap<String, String>,
    pub epsilon: f64,
    pub rule: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CatPrismAST {
    pub categories: Vec<Category>,
    pub metric: Metric,
    pub functor: FunctorMap,
}
