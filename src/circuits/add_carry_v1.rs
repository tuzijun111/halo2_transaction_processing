// use eth_types::Field;
// use halo2_proofs::{circuit::*, plonk::*};

// use super::super::chips::add_carry_v1::{AddCarryChip, AddCarryConfig};

// #[derive(Default)]
// struct AddCarryCircuit<F: Field> {
//     pub a: Vec<Value<F>>,
// }

// impl<F: Field> Circuit<F> for AddCarryCircuit<F> {
//     type Config = AddCarryConfig<F>;
//     type FloorPlanner = SimpleFloorPlanner;

//     fn without_witnesses(&self) -> Self {
//         Self::default()
//     }

//     fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
//         let col_a = meta.advice_column();
//         let col_b = meta.advice_column();
//         let col_c = meta.advice_column();
//         let constant = meta.fixed_column();
//         let carry_selector = meta.complex_selector();
//         let instance = meta.instance_column();

//         AddCarryChip::configure(
//             meta,
//             [col_a, col_b, col_c],
//             constant,
//             carry_selector,
//             instance,
//         )
//     }

//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<F>,
//     ) -> Result<(), Error> {
//         let chip = AddCarryChip::construct(config);

//         let (mut prev_b, mut prev_c) =
//             chip.assign_first_row(layouter.namespace(|| "load first row"))?;

//         for (i, a) in self.a.iter().enumerate() {
//             let (b, c) = chip.assign_advice_row(
//                 layouter.namespace(|| format!("load row {}", i)),
//                 *a,
//                 prev_b,
//                 prev_c,
//             )?;
//             prev_b = b;
//             prev_c = c;
//         }

//         // check computation result
//         chip.expose_public(layouter.namespace(|| "carry check"), &prev_b, 0)?;
//         chip.expose_public(layouter.namespace(|| "remain check"), &prev_c, 1)?;
//         Ok(())
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::AddCarryCircuit;
//     use halo2_proofs::{
//         circuit::Value,
//         dev::{FailureLocation, MockProver, VerifyFailure},
//         halo2curves::bn256::Fr as Fp,
//         plonk::Any,
//     };

//     #[test]
//     fn test_carry_1() {
//         let k = 4;

//         // a: new value
//         let a = vec![
//             // Value::known(Fp::from((1 << 16) - 1)),
//             Value::known(Fp::from(1)),
//             Value::known(Fp::from(1)),
//         ];
//         let public_inputs = vec![Fp::from(1), Fp::from(1)]; // initial accumulated values

//         let circuit = AddCarryCircuit::<Fp> { a };
//         let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
//         prover.assert_satisfied();
//         assert_eq!(prover.verify(), Ok(()));
//     }

//     #[test]
//     fn test_carry_2() {
//         let k = 4;

//         // now a[1] is 2, which will cause carry lo
//         let a = vec![
//             Value::known(Fp::from((1 << 16) - 1)),
//             Value::known(Fp::from(2)),
//         ];
//         let mut public_inputs = vec![Fp::from(1), Fp::from(0)]; // initial accumulated values

//         let circuit = AddCarryCircuit { a };
//         let invalid_prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
//         assert_eq!(
//             invalid_prover.verify(),
//             Err(vec![
//                 VerifyFailure::Permutation {
//                     column: (Any::advice(), 2).into(),
//                     location: FailureLocation::InRegion {
//                         region: (2, "adivce row for accumulating").into(),
//                         offset: 1
//                     }
//                 },
//                 VerifyFailure::Permutation {
//                     column: (Any::Instance, 0).into(),
//                     location: FailureLocation::OutsideRegion { row: 1 }
//                 },
//             ])
//         );

//         // Result should be 1, 1
//         public_inputs = vec![Fp::from(1), Fp::from(1)];
//         let valid_prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
//         valid_prover.assert_satisfied();
//     }
// }
