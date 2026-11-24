import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_2_1_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.ProductRule.Integ
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds.R1.ProductRule.L1

/-!
# `PartIII-a:T21/2/2/2/2/1/4`, assembly `WeightedProductRule`

Source: `the November 2 reference manuscript` (SP) lines 3060-3073.
The product rule follows from the integrability leaf `wprInteg` and the L¹ slope leaf `wprL1`
through `weightedProductRule_of`.
-/

open UnforcedLeray.Short.IIIa.E0 in
theorem weightedProductRule : UnforcedLeray.Short.IIIa.E0.WeightedProductRule :=
  weightedProductRule_of wprInteg wprL1
