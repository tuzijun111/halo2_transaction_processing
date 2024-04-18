use halo2_proofs::{halo2curves::ff::PrimeField, plonk::Expression};
// use gadgets::less_than::{LtChip, LtConfig, LtInstruction};
use super::super::chips::permutation_any::{PermAnyChip, PermAnyConfig};

use std::thread::sleep;
use std::{default, marker::PhantomData};

use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};

// const NUM_BYTES: usize = 5;

#[derive(Clone, Debug)]
pub struct TestCircuitConfig {
    q_enable: Vec<Selector>,
    q_perm: Vec<Selector>,

    values: Vec<Column<Advice>>, //  c_custkey, c_nationkey

    // perm: Vec<PermAnyConfig>,
    instance: Column<Instance>,
    instance_test: Column<Advice>,
}

#[derive(Debug, Clone)]
pub struct TestChip<F: PrimeField> {
    config: TestCircuitConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> TestChip<F> {
    pub fn construct(config: TestCircuitConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> TestCircuitConfig {
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        let instance_test = meta.advice_column();
        meta.enable_equality(instance_test);

        let mut q_enable = Vec::new();
        let mut q_perm = Vec::new();
        for _ in 0..1 {
            q_enable.push(meta.selector());
        }
        for _ in 0..2 {
            q_perm.push(meta.complex_selector());
        }

        let mut values = Vec::new();
        for _ in 0..3 {
            values.push(meta.advice_column());
        }

        // permutation check
        // meta.shuffle("permutation check", |meta| {
        //     // Inputs
        //     let q1 = meta.query_selector(q_perm[0]);
        //     let q2 = meta.query_selector(q_perm[1]);
        //     let input1 = meta.query_advice(values[0], Rotation::cur());

        //     let input2 = meta.query_advice(values[1], Rotation::cur());

        //     vec![(q1 * input1, q2 * input2)]
        // });

        meta.create_gate("accumulate constraint", |meta| {
            let q = meta.query_selector(q_enable[0]);
            let input1 = meta.query_advice(values[0], Rotation::cur());
            let input2 = meta.query_advice(values[1], Rotation::cur());

            vec![q * (input1 - input2)]
        });

        // PermAnyChip::configure(
        //     meta,
        //     q_perm[0],
        //     q_perm[1],
        //     values[0].clone(),
        //     values[1].clone(),
        // );

        TestCircuitConfig {
            q_enable,
            q_perm,
            values,

            instance,
            instance_test,
        }
    }

    pub fn assign(
        &self,
        // layouter: &mut impl Layouter<F>,
        layouter: &mut impl Layouter<F>,

        value1: Vec<u64>,
        value2: Vec<u64>,
        value3: Vec<u64>,
        // condition: Vec<u64>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "witness",
            |mut region| {
                //assign input values

                for i in 0..value1.len() {
                    self.config.q_enable[0].enable(&mut region, i)?;
                    // self.config.q_perm[0].enable(&mut region, i)?;
                    region.assign_advice(
                        || "v1",
                        self.config.values[0],
                        i,
                        || Value::known(F::from(value1[i])),
                    )?;
                }
                for i in 0..value2.len() {
                    // self.config.q_perm[1].enable(&mut region, i)?;
                    region.assign_advice(
                        || "v2",
                        self.config.values[1],
                        i,
                        || Value::known(F::from(value2[i])),
                    )?;
                }
                for i in 0..value3.len() {
                    region.assign_advice(
                        || "v3",
                        self.config.values[2],
                        i,
                        || Value::known(F::from(value3[i])),
                    )?;
                }

                // instance test

                let out = region.assign_advice(
                    || "test instance",
                    self.config.instance_test,
                    0,
                    || Value::known(F::from(1)),
                )?;
                Ok(out)
            },
        )
    }

    pub fn expose_public(
        &self,
        layouter: &mut impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

struct MyCircuit<F> {
    value1: Vec<u64>,
    value2: Vec<u64>,
    value3: Vec<u64>,

    // pub condition: Vec<u64>,
    _marker: PhantomData<F>,
}

impl<F: Copy + Default> Default for MyCircuit<F> {
    fn default() -> Self {
        Self {
            value1: Vec::new(),
            value2: Vec::new(),
            value3: Vec::new(),

            // condition: vec![Default::default(); 3],
            _marker: PhantomData,
        }
    }
}

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
    type Config = TestCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TestChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let test_chip = TestChip::construct(config);

        let out_cells = test_chip.assign(
            &mut layouter,
            self.value1.clone(),
            self.value2.clone(),
            self.value3.clone(),
        )?;

        test_chip.expose_public(&mut layouter, out_cells, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::MyCircuit;

    use chrono::{DateTime, NaiveDate, Utc};
    use halo2_proofs::{dev::MockProver, poly::Polynomial};
    use halo2curves::pasta::{pallas, vesta, EqAffine, Fp};
    use std::marker::PhantomData;

    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
            ConstraintSystem, Error, Instance,
        },
        poly::{
            commitment::{Params, ParamsProver},
            ipa::{
                commitment::{IPACommitmentScheme, ParamsIPA},
                multiopen::ProverIPA,
                strategy::SingleStrategy,
            },
            VerificationStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use rand::rngs::OsRng;
    use std::process;
    use std::time::Instant;
    use std::{fs::File, io::Write, path::Path};

    use halo2_proofs::{plonk::VerifyingKey, SerdeFormat};
    use std::io::BufWriter;
    use std::io::Cursor;

    fn generate_and_verify_proof<C: Circuit<Fp>>(
        k: u32,
        circuit: C,
        public_input: &[Fp], // Adjust the type according to your actual public input type
        proof_path: &str,
    ) {
        let params_path = "/home/cc/halo2-TPCH/src/params/param12";
        // Time to generate parameters
        // let params_time_start = Instant::now();
        // let params: ParamsIPA<vesta::Affine> = ParamsIPA::new(k);

        // let mut fd = std::fs::File::create(&params_path).unwrap();
        // params.write(&mut fd).unwrap();
        // println!("Time to generate params {:?}", params_time);

        // read params16
        let mut fd = std::fs::File::open(&params_path).unwrap();
        let params = ParamsIPA::<vesta::Affine>::read(&mut fd).unwrap();

        // Time to generate verification key (vk)
        let params_time_start = Instant::now();
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");

        let params_time = params_time_start.elapsed();
        println!("Time to generate vk {:?}", params_time);

        // Time to generate proving key (pk)
        let params_time_start = Instant::now();
        let pk = keygen_pk(&params, vk.clone(), &circuit).expect("keygen_pk should not fail");
        let params_time = params_time_start.elapsed();
        println!("Time to generate pk {:?}", params_time);

        //     // Proof generation
        //     let mut rng = OsRng;

        //     let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<_>>::init(vec![]);
        //     create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(
        //         &params,
        //         &pk,
        //         &[circuit],
        //         &[&[public_input]], // Adjust as necessary for your public input handling
        //         &mut rng,
        //         &mut transcript,
        //     )
        //     .expect("proof generation should not fail");
        //     let proof = transcript.finalize();

        //     // Write proof to file
        //     File::create(Path::new(proof_path))
        //         .expect("Failed to create proof file")
        //         .write_all(&proof)
        //         .expect("Failed to write proof");
        //     println!("Proof written to: {}", proof_path);

        //     // Proof verification
        //     let strategy = SingleStrategy::new(&params);
        //     let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        //     assert!(
        //         verify_proof(
        //             &params,
        //             pk.get_vk(),
        //             strategy,
        //             &[&[public_input]], // Adjust as necessary
        //             &mut transcript
        //         )
        //         .is_ok(),
        //         "Proof verification failed"
        //     );
    }

    #[test]
    fn test_1() {
        let k = 12;

        let value1: Vec<u64> = (1..=2).collect();
        let value2: Vec<u64> = (1..=2).collect();
        let value3 = vec![1, 2, 3, 40, 50];

        let circuit = MyCircuit::<Fp> {
            value1,
            value2,
            value3,
            _marker: PhantomData,
        };

        let public_input = vec![Fp::from(1)];

        // let test = true;
        let test = false;

        if test {
            let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
            prover.assert_satisfied();
        } else {
            let proof_path = "/home/cc/halo2-TPCH/src/proof/proof_test";
            generate_and_verify_proof(k, circuit, &public_input, proof_path);
        }
    }
}
