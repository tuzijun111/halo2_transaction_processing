// use super::super::chips::merkle_v2::{MerkleTreeV2Chip, MerkleTreeV2Config};
// use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};

// #[derive(Default)]
// struct MerkleTreeV2Circuit<F> {
//     pub leaf: Value<F>,
//     pub path_elements: Vec<Value<F>>,
//     pub path_indices: Vec<Value<F>>,
// }

// impl<F: FieldExt> Circuit<F> for MerkleTreeV2Circuit<F> {
//     type Config = MerkleTreeV2Config;
//     type FloorPlanner = SimpleFloorPlanner;

//     fn without_witnesses(&self) -> Self {
//         Self::default()
//     }

//     fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
//         let col_a = meta.advice_column();
//         let col_b = meta.advice_column();
//         let col_c = meta.advice_column();
//         let instance = meta.instance_column();
//         MerkleTreeV2Chip::configure(meta, [col_a, col_b, col_c], instance)
//     }

//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<F>,
//     ) -> Result<(), Error> {
//         let chip = MerkleTreeV2Chip::construct(config);
//         let leaf_cell = chip.assing_leaf(layouter.namespace(|| "assign leaf"), self.leaf)?;
//         chip.expose_public(layouter.namespace(|| "public leaf"), &leaf_cell, 0);

//         // apply it for level 0 of the merkle tree
//         // node cell passed as input is the leaf cell
//         let mut digest = chip.merkle_prove_layer(
//             layouter.namespace(|| "merkle_prove"),
//             &leaf_cell,
//             self.path_elements[0],
//             self.path_indices[0],
//         )?;

//         // apply it for the remaining levels of the merkle tree
//         // node cell passed as input is the digest cell
//         for i in 1..self.path_elements.len() {
//             digest = chip.merkle_prove_layer(
//                 layouter.namespace(|| "next level"),
//                 &digest,
//                 self.path_elements[i],
//                 self.path_indices[i],
//             )?;
//         }
//         chip.expose_public(layouter.namespace(|| "public root"), &digest, 1)?;
//         Ok(())
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::MerkleTreeV2Circuit;
//     use halo2_proofs::{circuit::Value, dev::MockProver, halo2curves::pasta::Fp};

//     #[test]
//     fn test_merkle_tree_2() {
//         let leaf = 99u64;
//         let elements = vec![1u64, 5u64, 6u64, 9u64, 9u64];
//         let indices = vec![0u64, 0u64, 0u64, 0u64, 0u64];
//         let digest: u64 = leaf + elements.iter().sum::<u64>();

//         let leaf_fp = Value::known(Fp::from(leaf));
//         let elements_fp: Vec<Value<Fp>> = elements
//             .iter()
//             .map(|x| Value::known(Fp::from(x.to_owned())))
//             .collect();
//         let indices_fp: Vec<Value<Fp>> = indices
//             .iter()
//             .map(|x| Value::known(Fp::from(x.to_owned())))
//             .collect();

//         let circuit = MerkleTreeV2Circuit {
//             leaf: leaf_fp,
//             path_elements: elements_fp,
//             path_indices: indices_fp,
//         };

//         let public_input = vec![Fp::from(leaf), Fp::from(digest)];
//         let prover = MockProver::run(10, &circuit, vec![public_input]).unwrap();
//         prover.assert_satisfied();
//     }
// }

// #[cfg(feature = "dev-graph")]
// #[test]
// fn print_merkle_tree_2() {
//     use halo2_proofs::halo2curves::pasta::Fp;
//     use plotters::prelude::*;

//     let root =
//         BitMapBackend::new("prints/merkle-tree-2-layout.png", (1024, 3096)).into_drawing_area();
//     root.fill(&WHITE).unwrap();
//     let root = root
//         .titled("Merkle Tree 2 Layout", ("sans-serif", 60))
//         .unwrap();

//     let leaf = 99u64;
//     let elements = vec![1u64, 5u64, 6u64, 9u64, 9u64];
//     let indices = vec![0u64, 0u64, 0u64, 0u64, 0u64];
//     let digest: u64 = leaf + elements.iter().sum::<u64>();

//     let leaf_fp = Value::known(Fp::from(leaf));
//     let elements_fp: Vec<Value<Fp>> = elements
//         .iter()
//         .map(|x| Value::known(Fp::from(x.to_owned())))
//         .collect();
//     let indices_fp: Vec<Value<Fp>> = indices
//         .iter()
//         .map(|x| Value::known(Fp::from(x.to_owned())))
//         .collect();

//     let circuit = MerkleTreeV2Circuit {
//         leaf: leaf_fp,
//         path_elements: elements_fp,
//         path_indices: indices_fp,
//     };

//     halo2_proofs::dev::CircuitLayout::default()
//         .render(4, &circuit, &root)
//         .unwrap();
// }
