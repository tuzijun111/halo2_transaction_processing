// use eth_types::Field;
// // use gadgets::less_than::{LtChip, LtConfig, LtInstruction};
// use crate::chips::is_zero::{IsZeroChip, IsZeroConfig};
// use gadgets::less_than::{LtChip, LtConfig, LtInstruction};
// use gadgets::lessthan_or_equal::{LtEqChip, LtEqConfig, LtEqInstruction};
// use gadgets::lessthan_or_equal_generic::{
//     LtEqGenericChip, LtEqGenericConfig, LtEqGenericInstruction,
// };

// use std::{default, marker::PhantomData};

// // use crate::chips::is_zero_v1::{IsZeroChip, IsZeroConfig};
// use crate::chips::is_zero_v2::{IsZeroV2Chip, IsZeroV2Config};
// use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};
// use itertools::iproduct;
// use std::cmp::Reverse;
// use std::collections::HashSet;

// use std::mem;

// const N: usize = 1;
// const NUM_BYTES: usize = 3;

// // #[derive(Default)]
// // We should use the selector to skip the row which does not satisfy shipdate values

// #[derive(Clone, Debug)]
// pub struct TestCircuitConfig<F: Field> {
//     q_enable: [Selector; 5],

//     part: [Column<Advice>; 3],     // p_partkey, p_type, p_name
//     supplier: [Column<Advice>; 2], // s_suppkey, s_nationkey
//     lineitem: [Column<Advice>; 6], // l_extendedprice, l_discount, l_partkey, l_suppkey, l_orderkey, l_quantity
//     partsupp: [Column<Advice>; 3], // ps_suppkey, ps_partkey, ps_supplycost,
//     orders: [Column<Advice>; 4],   // o_year, o_orderdate, o_orderkey, o_custkey
//     nation: [Column<Advice>; 3],   // n_nationkey, n_regionkey, n_name

//     condition: [Column<Advice>; 1], // r_name = ':2', o_orderdate between date '1995-01-01' and date '1996-12-31', p_type = ':3'

//     check: [Column<Advice>; 1],

//     groupby: [Column<Advice>; 2],

//     join_column: [Column<Advice>; 5],
//     disjoin_column: [Column<Advice>; 5],

//     amount: [Column<Advice>; 2],

//     p_condition: IsZeroConfig<F>,
//     // groupby_sort: LtEqGenericConfig<F, NUM_BYTES>,
//     // revenue_final: LtEqGenericConfig<F, NUM_BYTES>,
// }

// #[derive(Debug, Clone)]
// pub struct TestChip<F: Field> {
//     config: TestCircuitConfig<F>,
// }

// // conditions for filtering in tables: customer, orders,lineitem
// //   c_mktsegment = ':1', o_orderdate < date ':2', and l_shipdate > date ':2'

// // Circuits illustration
// // | l_orderkey |  l_extendedprice | l_discount | l_shipdate | ...
// // ------+-------+------------+------------------------+-------------------------------
// //    |     |       |         0              |  0

// impl<F: Field> TestChip<F> {
//     pub fn construct(config: TestCircuitConfig<F>) -> Self {
//         Self { config }
//     }

//     pub fn configure(meta: &mut ConstraintSystem<F>) -> TestCircuitConfig<F> {
//         let q_enable = [
//             meta.complex_selector(),
//             meta.complex_selector(),
//             meta.complex_selector(),
//             meta.complex_selector(),
//             meta.complex_selector(),
//         ];
//         let part = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];
//         let supplier = [meta.advice_column(), meta.advice_column()];
//         let lineitem = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];
//         let partsupp = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];
//         let orders = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];
//         let nation = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];

//         let condition = [meta.advice_column()];
//         let check = [meta.advice_column()];
//         let groupby = [meta.advice_column(), meta.advice_column()];

//         let join_column = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];

//         let disjoin_column = [
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//             meta.advice_column(),
//         ];
//         let amount = [meta.advice_column(), meta.advice_column()];
//         let is_zero_advice_column1 = meta.advice_column();

//         meta.enable_equality(condition[0]);
//         meta.enable_equality(check[0]);
//         for i in 0..2 {
//             meta.enable_equality(part[i]);
//             meta.enable_equality(supplier[i]);
//             meta.enable_equality(amount[i]);
//         }
//         for i in 0..3 {
//             meta.enable_equality(partsupp[i]);
//             meta.enable_equality(nation[i]);
//         }
//         for i in 0..4 {
//             meta.enable_equality(orders[i]);
//         }
//         for i in 0..6 {
//             meta.enable_equality(lineitem[i]);
//         }
//         for i in 0..join_column.len() {
//             meta.enable_equality(join_column[i]);
//             meta.enable_equality(disjoin_column[i]);
//         }

//         // p_name like '%:1%'
//         let p_condition = IsZeroChip::configure(
//             meta,
//             |meta| meta.query_selector(q_enable[0]), // this is the q_enable
//             |meta| {
//                 meta.query_advice(part[2], Rotation::cur())
//                     - meta.query_advice(condition[0], Rotation::cur())
//             }, // this is the value
//             is_zero_advice_column1, // this is the advice column that stores value_inv
//         );

//         // // gate for o_orderdate < date ':2' + interval '1' year
//         // meta.create_gate(
//         //     "verifies o_orderdate < date ':2' + interval '1' year", // just use less_than for testing here
//         //     |meta| {
//         //         let q_enable = meta.query_selector(q_enable);
//         //         let check = meta.query_advice(o1_check, Rotation::cur());
//         //         vec![q_enable * (lt_o1_condition.is_lt(meta, None) - check)]
//         //     },
//         // );

//         // // gate for o_orderdate >= date ':2'
//         // meta.create_gate("verifies o_orderdate < date ':2'", |meta| {
//         //     let q_enable = meta.query_selector(q_enable);
//         //     let check = meta.query_advice(o2_check, Rotation::cur());
//         //     vec![q_enable * (lt_o2_condition.is_lt(meta, None) - check)]
//         // });

//         // // gate for r_name = ':1'
//         // meta.create_gate("f(a, b) = if a == b {1} else {0}", |meta| {
//         //     let s = meta.query_selector(q_enable);
//         //     let output = meta.query_advice(r_check, Rotation::cur());
//         //     vec![
//         //         s.clone()
//         //             * (lt_r_condition.expr() * (output.clone() - Expression::Constant(F::ONE))), // in this case output == 1
//         //         s * (Expression::Constant(F::ONE) - lt_r_condition.expr()) * (output), // in this case output == 0
//         //     ]
//         // });

//         // // groupby
//         // let groupby_sort = LtEqGenericChip::configure(
//         //     meta,
//         //     |meta| meta.query_selector(q_sort),
//         //     |meta| vec![meta.query_advice(groupby_name, Rotation::prev())],
//         //     |meta| vec![meta.query_advice(groupby_name, Rotation::cur())],
//         // );

//         // let revenue_final = LtEqGenericChip::configure(
//         //     meta,
//         //     |meta| meta.query_selector(q_sort),
//         //     |meta| vec![meta.query_advice(sorted_revenue, Rotation::prev())],
//         //     |meta| vec![meta.query_advice(sorted_revenue, Rotation::cur())],
//         // );

//         TestCircuitConfig {
//             q_enable,
//             part,
//             supplier,
//             lineitem,
//             partsupp,
//             orders,
//             nation,
//             condition,
//             check,
//             groupby,
//             join_column,
//             disjoin_column,
//             amount,
//             p_condition,
//             // groupby_sort,
//             // revenue_final,
//         }
//     }

//     pub fn assign(
//         &self,
//         layouter: &mut impl Layouter<F>,
//         part: [[F; N]; 3],
//         supplier: [[F; N]; 2],
//         lineitem: [[F; N]; 6],
//         partsupp: [[F; N]; 3],
//         orders: [[F; N]; 4],
//         nation: [[F; N]; 3],

//         p_condition: F,
//     ) -> Result<(), Error> {
//         // Result<AssignedCell<F, F>, Error> {
//         let p_cond_chip = IsZeroChip::construct(self.config.p_condition.clone());
//         // let groupby_sort_chip = LtEqGenericChip::construct(self.config.groupby_sort.clone());
//         // let lt_revenue_final_chip = LtEqGenericChip::construct(self.config.revenue_final.clone());

//         // lt_o1_cond_chip.load(layouter)?;
//         // lt_o2_cond_chip.load(layouter)?;

//         layouter.assign_region(
//             || "witness",
//             |mut region| {
//                 // locally compute the values for conditional check
//                 let mut p_check: [F; N] = [F::from(0); N];
//                 // o2_condition<= x <= o1_condition

//                 for i in 0..part[0].len() {
//                     if part[2][i] == p_condition {
//                         p_check[i] = F::from(1);
//                     }
//                 }

//                 //assign input values
//                 for i in 0..part.len() {
//                     for j in 0..part[0].len() {
//                         region.assign_advice(
//                             || "p",
//                             self.config.part[i],
//                             i,
//                             || Value::known(part[i][j]),
//                         )?;
//                     }
//                 }
//                 for i in 0..supplier.len() {
//                     for j in 0..supplier[0].len() {
//                         region.assign_advice(
//                             || "s",
//                             self.config.supplier[i],
//                             i,
//                             || Value::known(supplier[i][j]),
//                         )?;
//                     }
//                 }
//                 for i in 0..lineitem.len() {
//                     for j in 0..lineitem[0].len() {
//                         region.assign_advice(
//                             || "l",
//                             self.config.lineitem[i],
//                             i,
//                             || Value::known(lineitem[i][j]),
//                         )?;
//                     }
//                 }
//                 for i in 0..partsupp.len() {
//                     for j in 0..partsupp[0].len() {
//                         region.assign_advice(
//                             || "ps",
//                             self.config.partsupp[i],
//                             i,
//                             || Value::known(partsupp[i][j]),
//                         )?;
//                     }
//                 }
//                 for i in 0..orders.len() {
//                     for j in 0..orders[0].len() {
//                         region.assign_advice(
//                             || "o",
//                             self.config.orders[i],
//                             i,
//                             || Value::known(orders[i][j]),
//                         )?;
//                     }
//                 }
//                 for i in 0..nation.len() {
//                     for j in 0..nation[0].len() {
//                         region.assign_advice(
//                             || "n",
//                             self.config.nation[i],
//                             i,
//                             || Value::known(nation[i][j]),
//                         )?;
//                     }
//                 }

//                 for i in 0..part[0].len() {
//                     p_cond_chip.assign(&mut region, i, Value::known(part[2][i] - p_condition))?;
//                     region.assign_advice(
//                         || "",
//                         self.config.condition[0],
//                         i,
//                         || Value::known(p_condition),
//                     )?;
//                     region.assign_advice(
//                         || "",
//                         self.config.check[0],
//                         i,
//                         || Value::known(p_check[i]),
//                     )?;
//                 }

//                 // compute values related to the join operation locally
//                 // translate the input into row-based values
//                 let mut p_combined: Vec<Vec<_>> = (0..part[0].len())
//                     .map(|i| part.iter().map(|row| row[i]).collect())
//                     .collect();
//                 let p_combined: Vec<Vec<_>> = p_combined // due to p_name like '%:1%'
//                     .into_iter()
//                     .filter(|row| row[2] == p_condition)
//                     .collect();

//                 let s_combined: Vec<Vec<_>> = (0..supplier[0].len())
//                     .map(|i| supplier.iter().map(|row| row[i]).collect())
//                     .collect();

//                 let l_combined: Vec<Vec<_>> = (0..lineitem[0].len())
//                     .map(|i| lineitem.iter().map(|row| row[i]).collect())
//                     .collect();
//                 let ps_combined: Vec<Vec<_>> = (0..partsupp[0].len())
//                     .map(|i| partsupp.iter().map(|row| row[i]).collect())
//                     .collect();
//                 let o_combined: Vec<Vec<_>> = (0..orders[0].len())
//                     .map(|i| orders.iter().map(|row| row[i]).collect())
//                     .collect();
//                 let n_combined: Vec<Vec<_>> = (0..nation[0].len())
//                     .map(|i| nation.iter().map(|row| row[i]).collect())
//                     .collect();

//                 //create the values for join and disjoin
//                 let mut join_value: Vec<Vec<_>> = vec![Default::default(); 12];
//                 let mut disjoin_value: Vec<Vec<_>> = vec![Default::default(); 12];
//                 // s_suppkey = l_suppkey
//                 // and ps_suppkey = l_suppkey
//                 // and ps_partkey = l_partkey
//                 // and p_partkey = l_partkey
//                 // and o_orderkey = l_orderkey
//                 // and s_nationkey = n_nationkey
//                 let mut combined = Vec::new();
//                 combined.push(l_combined); // its length is 6
//                 combined.push(p_combined); // 3
//                 combined.push(s_combined); // 2
//                 combined.push(o_combined); // 4
//                 combined.push(ps_combined); // 3
//                 combined.push(n_combined); // 3

//                 // (input1 index, input2 index, join attribute index of input1, join attribute of input2)
//                 let index = [
//                     (0, 1, 2, 0), //   p_partkey = l_partkey
//                     (0, 2, 3, 0), // s_suppkey = l_suppkey
//                     (0, 3, 4, 2), // o_orderkey = l_orderkey
//                     (0, 4, 3, 0), // ps_suppkey = l_suppkey
//                     (0, 4, 2, 1), //  ps_partkey = l_partkey
//                     (2, 5, 1, 0), // s_nationkey = n_nationkey
//                 ];

//                 for i in 0..index.len() {
//                     for val in combined[index[i].0].iter() {
//                         if let Some(_) = combined[index[i].1]
//                             .iter()
//                             .find(|v| v[index[i].3] == val[index[i].2])
//                         {
//                             join_value[i * 2].push(val); // join values
//                         } else {
//                             disjoin_value[i * 2].push(val); // disjoin values
//                         }
//                     }
//                     for val in combined[index[i].1].iter() {
//                         if let Some(_) = combined[index[i].0]
//                             .iter()
//                             .find(|v| v[index[i].2] == val[index[i].3])
//                         {
//                             join_value[i * 2 + 1].push(val);
//                         } else {
//                             disjoin_value[i * 2 + 1].push(val);
//                         }
//                     }
//                 }

//                 // compute final table by applying all joins
//                 let join_index = [
//                     (0, 1, 2, 0),         //   p_partkey = l_partkey
//                     (0, 2, 3, 0),         // s_suppkey = l_suppkey
//                     (0, 3, 4, 2),         // o_orderkey = l_orderkey
//                     (0, 4, 3, 0), // (0, 4, 2, 1),        // ps_suppkey = l_suppkey  and  ps_partkey = l_partkey
//                     (2, 5, 6 + 3 + 1, 0), // s_nationkey = n_nationkey
//                 ];
//                 fn join_vectors<F>(
//                     vectors: &[Vec<Vec<F>>],
//                     join_index: &[(usize, usize, usize, usize)],
//                 ) -> Vec<Vec<F>>
//                 where
//                     F: Clone + PartialEq,
//                 {
//                     let mut join_result = vectors[0].to_vec();

//                     for i in 1..vectors.len() {
//                         let mut next_join = Vec::new();

//                         for ab in join_result.iter() {
//                             for c in vectors[i].iter() {
//                                 if i == 4 {
//                                     // two join with 4, i.e. (0, 4, 3, 0) and (0, 4, 2, 1),
//                                     if ab[3] == c[0] && ab[2] == c[1] {
//                                         let mut joined = ab.to_vec();
//                                         joined.extend_from_slice(c);
//                                         next_join.push(joined);
//                                     }
//                                 } else {
//                                     if ab[join_index[i - 1].2] == c[join_index[i - 1].3] {
//                                         let mut joined = ab.to_vec();
//                                         joined.extend_from_slice(c);
//                                         next_join.push(joined);
//                                     }
//                                 }
//                             }
//                         }

//                         join_result = next_join;
//                     }

//                     join_result
//                 }

//                 let mut cartesian_product = join_vectors(&combined, &join_index);

//                 println!(
//                     "product: {:?}, {:?}",
//                     cartesian_product.len(),
//                     cartesian_product[0].len()
//                 );

//                 // add volumn column into cartesian_product: l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity as amount
//                 for i in 0..cartesian_product.len() {
//                     let amount = cartesian_product[i][0]
//                         * (F::from(1000) - cartesian_product[i][1])
//                         - cartesian_product[i][9] * cartesian_product[i][5];
//                     cartesian_product[i].push(amount); // cartesian_product[i][22] = amount
//                 }
//                 // cartesian_product[i][13] : extract(year from o_orderdate) as o_year,
//                 // cartesian_product[i][21] : n2.n_name as nation

//                 // group by o_year
//                 let x = F::from(1);
//                 cartesian_product.sort_by_key(|v| v[13] + v[21]);

//                 // for i in 0..cartesian_product.len() {
//                 //     let value_21 = cartesian_product[i][21];
//                 //     let new_value = if value_21 == x {
//                 //         cartesian_product[i][22]
//                 //     } else {
//                 //         cartesian_product[i][0]
//                 //     };

//                 //     cartesian_product[i].push(new_value);
//                 // }

//                 // for i in 0..cartesian_product.len() {
//                 //     if i == 0 {
//                 //         self.config.q_enable[1].enable(&mut region, i)?;
//                 //         revenue.push(cartesian_product5[i].1 * cartesian_product5[i].2);
//                 //         revenue.push(cartesian_product5[i].1 * cartesian_product5[i].2);
//                 //     // l_extendedprice * (1 - l_discount)
//                 //     } else {
//                 //         self.config.q_sort.enable(&mut region, i)?;
//                 //         groupby_sort_chip.assign(
//                 //             &mut region,
//                 //             i,
//                 //             &[cartesian_product5[i - 1].10],
//                 //             &[cartesian_product5[i].10],
//                 //         )?;

//                 //         // check if it is the first value
//                 //         if cartesian_product5[i - 1].10 == cartesian_product5[i].10 {
//                 //             self.config.q_first.enable(&mut region, i)?;
//                 //             revenue.push(cartesian_product5[i].1 * cartesian_product5[i].2);
//                 //         } else {
//                 //             self.config.q_nonfirst.enable(&mut region, i)?;
//                 //             revenue.push(
//                 //                 revenue[i - 1] + cartesian_product5[i].1 * cartesian_product5[i].2,
//                 //             );
//                 //         }
//                 //     }
//                 //     // assign revenue column
//                 //     region.assign_advice(
//                 //         || "revenue",
//                 //         self.config.revenue,
//                 //         i,
//                 //         || Value::known(revenue[i]),
//                 //     )?;

//                 //     region.assign_advice(
//                 //         || "groupby_name",
//                 //         self.config.groupby_name,
//                 //         i,
//                 //         || Value::known(cartesian_product5[i].10),
//                 //     )?;

//                 //     region.assign_advice(
//                 //         || "groupby_l_extendedprice",
//                 //         self.config.groupby_extendedprice,
//                 //         i,
//                 //         || Value::known(cartesian_product5[i].1),
//                 //     )?;

//                 //     region.assign_advice(
//                 //         || "groupby_l_discount",
//                 //         self.config.groupby_discount,
//                 //         i,
//                 //         || Value::known(cartesian_product5[i].2),
//                 //     )?;
//                 // }

//                 // // generate revenue_final
//                 // // println!("product: {:?}", cartesian_product5);
//                 // let mut revenue_final = Vec::new(); // by removing intermediate revenue values, i.e. only keep the final revenue of each group
//                 // if revenue.len() > 0 {
//                 //     for i in 0..revenue.len() - 1 {
//                 //         if cartesian_product5[i].10 != cartesian_product5[i + 1].10 {
//                 //             revenue_final.push((cartesian_product5[i].10, revenue[i]))
//                 //         }
//                 //     }

//                 //     revenue_final.push((
//                 //         cartesian_product5[revenue.len() - 1].10,
//                 //         revenue[revenue.len() - 1],
//                 //     ));
//                 // }

//                 // // order by revenue desc

//                 // revenue_final.sort_by_key(|&(value, _)| Reverse(value));

//                 // // assign values of equal check for verifying if revenue_final is sorted
//                 // let mut equal_check: Vec<F> = Vec::new();

//                 // if revenue_final.len() == 1 {
//                 //     equal_check.push(F::from(0)); // 0 assigned to the first value in equal_check
//                 // } else {
//                 //     equal_check.push(F::from(0));
//                 //     for i in 1..revenue_final.len() {
//                 //         if revenue_final[i] == revenue_final[i - 1] {
//                 //             equal_check.push(F::from(1));
//                 //         } else {
//                 //             equal_check.push(F::from(0))
//                 //         }
//                 //     }
//                 // }
//                 // // println!("revenue: {:?}", revenue_final);
//                 // // println!("equal check: {:?}", equal_check);

//                 // // assign sorted revenue and orderdate
//                 // for i in 0..revenue_final.len() {
//                 //     region.assign_advice(
//                 //         || "sorted_revenue",
//                 //         self.config.sorted_revenue,
//                 //         i,
//                 //         || Value::known(revenue_final[i].1),
//                 //     )?;

//                 //     region.assign_advice(
//                 //         || "equal_check",
//                 //         self.config.equal_check,
//                 //         i,
//                 //         || Value::known(equal_check[i]),
//                 //     )?;

//                 //     if i != 0 {
//                 //         self.config.q_sort_final.enable(&mut region, i)?;
//                 //         lt_revenue_final_chip.assign(
//                 //             &mut region,
//                 //             i,
//                 //             &[revenue_final[i].1],
//                 //             &[revenue_final[i - 1].1],
//                 //         )?;
//                 //     }
//                 // }

//                 Ok(())
//             },
//         )
//     }

//     // pub fn expose_public(
//     //     &self,
//     //     layouter: &mut impl Layouter<F>,
//     //     cell: AssignedCell<F, F>,
//     //     row: usize,
//     // ) -> Result<(), Error> {
//     //     layouter.constrain_instance(cell.cell(), self.config.instance, row)
//     // }
// }

// struct MyCircuit<F: Copy> {
//     part: [[F; N]; 3],
//     supplier: [[F; N]; 2],
//     lineitem: [[F; N]; 6],
//     partsupp: [[F; N]; 3],
//     orders: [[F; N]; 4],
//     nation: [[F; N]; 3],

//     pub p_condition: F,
//     _marker: PhantomData<F>,
// }

// impl<F: Copy + Default> Default for MyCircuit<F> {
//     fn default() -> Self {
//         Self {
//             part: [Default::default(); 3],
//             supplier: [Default::default(); 2],
//             lineitem: [Default::default(); 6],
//             partsupp: [Default::default(); 3],
//             orders: [Default::default(); 4],
//             nation: [Default::default(); 3],

//             p_condition: Default::default(),
//             _marker: PhantomData,
//         }
//     }
// }

// impl<F: Field> Circuit<F> for MyCircuit<F> {
//     type Config = TestCircuitConfig<F>;
//     type FloorPlanner = SimpleFloorPlanner;

//     fn without_witnesses(&self) -> Self {
//         Self::default()
//     }

//     fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
//         TestChip::configure(meta)
//     }

//     fn synthesize(
//         &self,
//         config: Self::Config,
//         mut layouter: impl Layouter<F>,
//     ) -> Result<(), Error> {
//         let test_chip = TestChip::construct(config);

//         let out_b_cells = test_chip.assign(
//             &mut layouter,
//             self.part,
//             self.supplier,
//             self.lineitem,
//             self.partsupp,
//             self.orders,
//             self.nation,
//             self.p_condition,
//         )?;

//         // for (i, cell) in out_b_cells.iter().enumerate() {
//         //     test_chip.expose_public(&mut layouter, cell.clone(), i)?;
//         // }

//         // test_chip.expose_public(&mut layouter, out_b_cell, 0)?;

//         Ok(())
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::MyCircuit;
//     use super::N;
//     // use rand::Rng;
//     // use halo2_proofs::poly::commitment::Params
//     use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr as Fp};

//     use std::marker::PhantomData;

//     #[test]
//     fn test_1() {
//         let k = 10;
//         // let mut rng = rand::thread_rng();

//         let part = [[Fp::from(1); N]; 3];
//         let supplier = [[Fp::from(1); N]; 2];
//         let lineitem = [[Fp::from(1); N]; 6];
//         let partsupp = [[Fp::from(1); N]; 3];
//         let orders = [[Fp::from(1); N]; 4];
//         let nation = [[Fp::from(1); N]; 3];

//         let p_condition = Fp::from(1);

//         let circuit = MyCircuit::<Fp> {
//             part,
//             supplier,
//             lineitem,
//             partsupp,
//             orders,
//             nation,

//             p_condition,
//             _marker: PhantomData,
//         };

//         // let z = [Fp::from(1 * (N as u64))];
//         // let z = [
//         //     Fp::from(0),
//         //     Fp::from(1),
//         //     Fp::from(0),
//         //     Fp::from(0),
//         //     Fp::from(1),
//         // ];

//         // let prover = MockProver::run(k, &circuit, vec![z.to_vec()]).unwrap();
//         let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//         prover.assert_satisfied();
//     }
// }
// // time cargo test --package halo2-experiments --lib -- sql::q3_final_v1::tests::test_1 --exact --nocapture
