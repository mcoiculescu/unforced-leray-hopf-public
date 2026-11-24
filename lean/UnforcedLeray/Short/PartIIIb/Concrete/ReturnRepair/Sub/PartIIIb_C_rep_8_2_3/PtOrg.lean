import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1_4_1

/-!
# `PartIII-b:C/rep/8/2/3/2`: the pointwise weighted train bound `TMPt`, organized

Source of record: `the November 2 reference manuscript` (73 pages).
* 5464-5465, 5477-5482: the weighted train coefficient `𝔴_4` (`trainWeight 4`): `(1+|η|)^4` times
  the derivatives of order `≤ 4` in `(σ, q, η)`, `σ = log s`, of `v`, `p_cyl`, `ψ`; its bound is a
  viscosity polynomial `P_ν = Cν^{-k}` on the young range `0 < s ≤ 1/ν`.
* 5484-5495: the young train is the summed Gaussian train (`c = ν⁻²`, `a = 1+νs ≤ 2.1` on
  `s ≤ 1.1/ν`) up to the young-train comparison, Part I `sct:fixed-band` (468-478, `d = (v - V_c^p,
  ω - curl V_c^p, ∇(p - p_c^p))`, all `∂_σ^ℓ D^j`, sup norm).
* Part I `sct:transverse` (460-467): the fields `ψ, v, p` and their fixed derivatives have the
  transverse tails `P_S{e^{-bl/c} + e^{-bl²/(C₀+νS)}}` for `|η| ≥ C/ν + 2 + l`; these supply the
  transverse weight `(1+|η|)^4`.

## The route

1. (`DilJetBound`) `σ = log s`: the derivatives in `(σ, q, η)` of `F(e^σ, q, η)` are bounded by
   `j!(1+s)^j` times the joint derivatives of `(s, q, η) ↦ F(s, q, η)` of order `≤ j`
   (`norm_iteratedFDeriv_comp_le'`).
2. (`PartI.jointFromAgeJets`, proved; `JointAgeVec` for the velocity) the joint derivatives are
   bounded by the age/space jets `∂_s^ℓ D^m` (`PartI.ageJet`).
3. (`WJetV`, `WJetP`, `WJetPsi`) the weighted age/space jets `(1+|η|)^4 ‖∂_s^ℓ D^m F‖ ≤ P_ν` on
   `0 < s ≤ 1/ν`:
   * tail region `|η| ≥ C_p/ν + 2`: `TailW` (Part I `sct:transverse` with `l = |η| - C_p/ν - 2`,
     `S = 1/ν`, `c = ν⁻²`);
   * band region `|η| < C_p/ν + 2`: the weight is `≤ (C_p/ν + 3)^4`, and
     - `v`: `SupV` = `v - V_c^p` (Part I `sct:fixed-band`) plus `V_c^p` (Gaussian, `IIb.vcJetSup_proof`);
     - `p`, spatial order `≥ 1`: `BandP` from `∇(p - p_c^p)` (`FixedBandP`, Part I
       `sct:fixed-band`), `GradJetShift` and the Gaussian pressure `p_c^p = Σ_j p_j` (`PcJetSup`,
       through the theta factorization `PcTheta` and `IIb.tt`);
     - `ψ`, spatial order `≥ 1`: `∇ψ = ∇^⊥`-rotated `v` (`StreamShift`);
     - `p`, `ψ`, spatial order `0`: the fundamental theorem of calculus in `η` from the tail
       boundary `η* = C_p/ν + 2` (`EtaSegment`).
4. (`tmPt_of`, proved here) assembly along the sequence: `ν_n → 0`, the BUC class of the actual
   train (`IsActualLevel.regime.train_buc`), `ν_n ≤ 1`.

**Proved here:** `tp_unif` (uniformization of finitely many `(C, k, a)`), `tmPt_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-! ## 1. Generic calculus -/

/-- **(A1) The dilation chain rule** (source 5464-5465: the chart derivatives are taken in
`σ = log s`, `∂_σ = s∂_s`).  For `G` jointly `C^∞` on `(0,∞) × ℝ²`,
`‖D^j_{(σ,x)} G(e^σ, x)‖ ≤ j! (Σ_{i≤j} ‖D^i G(s,x)‖) (1+s)^j` at `σ = log s`.
Proof: `norm_iteratedFDeriv_comp_le'` with `t = Ioi 0 ×ˢ univ` (open: `iteratedFDerivWithin`
is `iteratedFDeriv` there), the inner map `(σ,x) ↦ (e^σ, x)` has `‖D¹‖ ≤ max(e^σ,1) ≤ 1+s` and
`‖D^i‖ ≤ e^σ = s ≤ (1+s)^i` for `i ≥ 2`. -/
def DilJetBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : ℝ × (ℝ × ℝ) → E),
    ContDiffOn ℝ ∞ G (Ioi 0 ×ˢ univ) → ∀ (j : ℕ) (s : ℝ), 0 < s → ∀ x : ℝ × ℝ,
      ‖iteratedFDeriv ℝ j (fun z : ℝ × (ℝ × ℝ) => G (Real.exp z.1, z.2)) (Real.log s, x)‖ ≤
        (j.factorial : ℝ) * (∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i G (s, x)‖) *
          (1 + s) ^ j

/-- **(A2) The joint derivative from the age jets, for a vector field** (the vector form of
`PartI.JointFromAgeJets`, `Short/PartI/Sub/PartI_TrainHeatFixed.lean:89`, proved as
`PartI.jointFromAgeJets`).  Proof: the two components (`contDiffOn_piLp`), `PartI.jointFromAgeJets`
for each, `‖M‖ ≤ Σ_k ‖proj_k ∘ M‖` for a multilinear map into `EuclideanSpace ℝ (Fin 2)`, and
`PartIIa.fvs_ageJet_proj_le` for the jets of a component. -/
def JointAgeVec : Prop :=
  ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ F : ℝ → Plane → UnforcedLeray.Train.Vec,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => F x.1 x.2) y‖ ≤
        K * ∑ ℓ ∈ Finset.range (i + 1), ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) F y.1 y.2‖

/-- **(A3) The age jets from the joint derivative** (generic calculus, the converse of
`PartI.JointFromAgeJets`): `∂_s^ℓ D^m F(s,z)` is the joint derivative `D^{ℓ+m}` of
`(s,z) ↦ F(s,z)` evaluated on `ℓ` copies of `e_s = (1,0)` and on `(0,h_i)`, so its norm is at most
`‖D^{ℓ+m}(s,z)‖`. -/
def AgeJetLeJoint : Prop :=
  ∀ F : ℝ → Plane → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (ℓ m : ℕ) (s : ℝ), 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m F s z‖ ≤
        ‖iteratedFDeriv ℝ (ℓ + m) (fun x : ℝ × Plane => F x.1 x.2) (s, z)‖

/-- **(A4) Stream jets from velocity jets** (source 2045-2051, `v = ∇^⊥ψ`): for a stream pair
(`IIb.IsStreamPair`: joint smoothness, `v = (-∂_ηψ, ∂_qψ)`), the spatial derivative of
`z ↦ ∂_s^ℓψ(s,z)` is `T(∂_s^ℓ v(s,z))`, `T w h = h.1 w₁ - h.2 w₀`, `‖T‖ ≤ 2`
(`IIb.psiQSwap_proof`, `IIb.psiEtaSwap_proof`), so `‖∂_s^ℓ D^{m+1}ψ‖ ≤ 2‖∂_s^ℓ D^m v‖`
(`norm_iteratedFDeriv_fderiv`, `ContinuousLinearMap.iteratedFDeriv_comp_left`). -/
def StreamShift : Prop :=
  ∀ (ψ : ℝ → Plane → ℝ) (v : ℝ → Plane → UnforcedLeray.Train.Vec),
    UnforcedLeray.Short.IIb.IsStreamPair ψ v →
    ∀ (ℓ m : ℕ) (s : ℝ), 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1) ψ s z‖ ≤
        2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m v s z‖

/-- **(A5) Scalar jets from gradient jets** (calculus): for `F` jointly `C^∞`,
`‖∂_s^ℓ D^{m+1}F‖ ≤ 2‖∂_s^ℓ D^m ∇F‖` (`∇ = Train.gradS` in the slice; `(F, ∇^⊥F)` is a stream
pair and `∇^⊥F` is the rotation of `∇F` by a linear isometry). -/
def GradJetShift : Prop :=
  ∀ F : ℝ → Plane → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (ℓ m : ℕ) (s : ℝ), 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1) F s z‖ ≤
        2 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m
          (fun r w => UnforcedLeray.Train.gradS (F r) w) s z‖

/-- **(A6) The fundamental theorem of calculus in `η`** (calculus): for `F` jointly `C^∞`, if
`‖∂_s^l D F(s,(q,t))‖ ≤ B` for `t` between `a` and `b`, then
`|∂_s^l F(s,(q,a))| ≤ |∂_s^l F(s,(q,b))| + B|a-b|`
(`norm_image_sub_le_of_norm_deriv_le_segment'`; `‖ageJet l 0 F s z‖ = |∂_s^lF|`). -/
def EtaSegment : Prop :=
  ∀ F : ℝ → Plane → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (l : ℕ) (s : ℝ), 0 < s → ∀ q a b B : ℝ,
      (∀ t ∈ uIcc a b, ‖UnforcedLeray.Short.PartI.ageJet l 1 F s (q, t)‖ ≤ B) →
      ‖UnforcedLeray.Short.PartI.ageJet l 0 F s (q, a)‖ ≤
        ‖UnforcedLeray.Short.PartI.ageJet l 0 F s (q, b)‖ + B * |a - b|

/-! ## 2. The Part I inputs at `c = ν⁻²`, `S = 1/ν` -/

/-- **Weighted tails** (Part I `sct:transverse`, source 460-467, with `S_* = 1/ν`, `c = ν⁻²`,
`l = |η| - C_p/ν - 2`): for `|η| ≥ C_p/ν + 2`, `(1+|η|)^4` times the jets `∂_s^ℓ D^m` of
`v, p, ψ` is `≤ Cν^{-k}` on `0 < s ≤ 1/ν` (`(A + l)^4 ≤ 8(A^4 + l^4)`, `l^4 e^{-bν²l} ≤ 24(bν²)^{-4}`,
`l^4 e^{-bl²/(C₀+1)} ≤ 2((C₀+1)/b)²`, `polyPS C N ν ν⁻² ν⁻¹ ≤ C6^Nν^{-3N}`). -/
def TailW : Prop :=
  ∀ ℓ m : ℕ, ∃ (Cp C : ℝ) (k : ℕ) (a : ℝ), 0 < Cp ∧ 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane, Cp / ν + 2 ≤ |z.2| →
        (1 + |z.2|) ^ 4 * (‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ +
          ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ +
          ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖) ≤ C * ν⁻¹ ^ k

/-- **Velocity jets on the young range** (source 5484-5492; Part I `sct:fixed-band` 468-478 for
`v - V_c^p`, and the Gaussian `V_c^p = Σ_jV_j` with `a = 1+νs ≤ 2`): `‖∂_s^ℓ D^m v‖ ≤ Cν^{-k}`
for `0 < s ≤ 1/ν`, every `z`. -/
def SupV : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ ≤ C * ν⁻¹ ^ k

/-- **Pressure difference jets** (Part I `sct:fixed-band`, source 468-478, the component
`∇(p - p_c^p)` of `d`, `L = ℓ`, `k = m`, weight `m = 0`, sup part; `∂_σ = ν⁻¹∂_s`,
`e^{C_Σ/ν - b_Σν^{-4}} ≤ 1` for small `ν`). -/
def FixedBandP : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        ‖UnforcedLeray.Short.PartI.ageJet ℓ m (fun r w => UnforcedLeray.Train.gradS
            (fun w' => tr.p r w' - UnforcedLeray.Train.pc ν (cOf ν) r w') w) s z‖ ≤ C * ν⁻¹ ^ k

/-! ## 3. The Gaussian pressure `p_c^p = Σ_j p_j` (source 4963-4968, 5484-5486) -/

/-- **Theta factorization of the summed Gaussian pressure** (source 4966-4968:
`p_j = -a⁻³e^{-|x_j|²/(2a)}`, `a = 1+νs`): `p_c^p(s,q,η) = -a⁻³ e^{-η²/(2a)} Σ_n e^{-(q-nc)²/(2a)}`,
the last factor `IIb.tt c 0 ((2a)⁻¹, q)` (`Short/PartII-b/Sub/PartII-b_G4_3_6_1_4_1.lean:61`). -/
def PcTheta : Prop :=
  ∀ ν c s : ℝ, 0 < ν → 0 < c → 0 ≤ s → ∀ z : Plane,
    UnforcedLeray.Train.pc ν c s z =
      -((1 + ν * s) ^ 3)⁻¹ * Real.exp (-z.2 ^ 2 / (2 * (1 + ν * s))) *
        UnforcedLeray.Short.IIb.tt c 0 ((2 * (1 + ν * s))⁻¹, z.1)

/-- **Derivatives of the theta sums** `T_j(u,q) = Σ_n (q-nc)^j e^{-u(q-nc)²}` on `1/5 ≤ u ≤ 1`,
uniformly in the period `c ≥ 2` (the Gaussian lattice sums of source 4963-4968 with separation
`c = ν⁻²`). -/
def TtJetBound : Prop :=
  ∀ i j : ℕ, ∃ K : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ x : ℝ × ℝ, 1 / 5 ≤ x.1 → x.1 ≤ 1 →
    ‖iteratedFDeriv ℝ i (UnforcedLeray.Short.IIb.tt c j) x‖ ≤ K

/-- **The Gaussian envelope** `-a⁻³e^{-η²/(2a)}`, `a = 1+νs`: bounded joint derivatives of each
order on `0 < s ≤ 1/ν`, uniformly in `ν ≤ 1` (each `∂_s` carries `ν`; `poly(η)e^{-η²/4}` is bounded). -/
def PcEnvJet : Prop :=
  ∀ n : ℕ, ∃ K : ℝ, ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 / ν →
    ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane =>
        -((1 + ν * x.1) ^ 3)⁻¹ * Real.exp (-x.2.2 ^ 2 / (2 * (1 + ν * x.1)))) y‖ ≤ K

/-- **The theta factor in the age variable** `(s,q,η) ↦ T_0((2(1+νs))⁻¹, q)`: bounded joint
derivatives of each order on `0 < s ≤ 1/ν` (`u ∈ [1/4, 1/2]`), uniformly in `ν ≤ 1/2`
(`c = ν⁻² ≥ 4`). -/
def TtCompJet : Prop :=
  ∀ n : ℕ, ∃ K : ℝ, ∀ ν : ℝ, 0 < ν → ν ≤ 1 / 2 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 / ν →
    ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane =>
        UnforcedLeray.Short.IIb.tt (cOf ν) 0 ((2 * (1 + ν * x.1))⁻¹, x.2.1)) y‖ ≤ K

/-- **Joint derivatives of the Gaussian pressure** on the young range, uniformly in `ν ≤ 1/2`. -/
def PcJointJet : Prop :=
  ∀ n : ℕ, ∃ K : ℝ, ∀ ν : ℝ, 0 < ν → ν ≤ 1 / 2 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 / ν →
    ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν (cOf ν) x.1 x.2) y‖ ≤ K

/-- **Joint smoothness of the Gaussian pressure** for `s > 0` (`PcTheta` and
`IIb.contDiffOn_tt_infty`). -/
def PcSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c →
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν c x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **Age jets of the Gaussian pressure** on the young range. -/
def PcJetSup : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m
          (fun r w => UnforcedLeray.Train.pc ν (cOf ν) r w) s z‖ ≤ C * ν⁻¹ ^ k

/-- **Pressure jets of positive spatial order** on the young range (source 5484-5492:
`p = (p - p_c^p) + p_c^p`; `FixedBandP` with `GradJetShift`, and `PcJetSup`). -/
def BandP : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1) tr.p s z‖ ≤ C * ν⁻¹ ^ k

/-! ## 4. The weighted age jets of the three fields -/

/-- **Weighted velocity jets** (source 5477-5482, 5484-5495, 460-478): `(1+|η|)^4‖∂_s^ℓD^m v‖ ≤
Cν^{-k}` on `0 < s ≤ 1/ν`, every `z`. -/
def WJetV : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.v s z‖ ≤ C * ν⁻¹ ^ k

/-- **Weighted pressure jets** (as `WJetV`, for the decaying pressure `p_cyl = tr.p`). -/
def WJetP : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.p s z‖ ≤ C * ν⁻¹ ^ k

/-- **Weighted stream jets** (as `WJetV`, for the decaying stream `ψ = tr.ψ`). -/
def WJetPsi : Prop :=
  ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ ν : ℝ, 0 < ν → ν ≤ a →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (cOf ν), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ 1 / ν → ∀ z : Plane,
        (1 + |z.2|) ^ 4 * ‖UnforcedLeray.Short.PartI.ageJet ℓ m tr.ψ s z‖ ≤ C * ν⁻¹ ^ k

/-! ## 5. The weighted dilation jets and the assembly -/

/-- **Weighted dilation jets of one train field** `F L` (`F = trainFv, trainFp, trainFpsi`;
source 5464-5465, 5477-5482): `(1+|η|)^4‖D^j_{(σ,q,η)}F(log s, q, η)‖ ≤ Cν^{-k}` for `j ≤ 4`,
`0 < s ≤ 1/ν`, uniformly over the levels with a BUC train and `ν ≤ a`. -/
def WDil {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ReturnLevel → ℝ × (ℝ × ℝ) → E) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ ∀ L : ReturnLevel,
    UnforcedLeray.Short.PartI.IsBUCTrain L.train → L.ν ≤ a → ∀ j : ℕ, j < 5 →
      ∀ p : Chart, 0 < p.1 → p.1 ≤ 1 / L.ν →
        (1 + |p.2.2|) ^ 4 * ‖iteratedFDeriv ℝ j (F L) (Real.log p.1, p.2)‖ ≤ C * L.ν⁻¹ ^ k

/-- **Uniformization of finitely many constants** (order of choice: the constants of each jet
`(ℓ, m)` with `ℓ, m ≤ N` are merged; `C` by a sum of absolute values, `k` by a sum, the threshold
by `min 1 (Σ a⁻¹)⁻¹`).  The predicate must be monotone in `C ≥ 0`, `k` and the threshold
`a ≤ 1` (true for every bound `C ν⁻¹^k` over `0 < ν ≤ a`). -/
theorem tp_unif {P : ℕ → ℕ → ℝ → ℕ → ℝ → Prop}
    (hmono : ∀ (ℓ m : ℕ) (C C' : ℝ) (k k' : ℕ) (a a' : ℝ), C ≤ C' → 0 ≤ C' → k ≤ k' →
      a' ≤ a → a' ≤ 1 → 0 < a' → P ℓ m C k a → P ℓ m C' k' a')
    (h : ∀ ℓ m : ℕ, ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 < a ∧ P ℓ m C k a) (N : ℕ) :
    ∃ (C : ℝ) (k : ℕ) (a : ℝ), 0 ≤ C ∧ 0 < a ∧ a ≤ 1 ∧
      ∀ ℓ m : ℕ, ℓ ≤ N → m ≤ N → P ℓ m C k a := by
  choose C k a ha hP using h
  set S : Finset ℕ := Finset.range (N + 1) with hS
  have hpos : 0 < ∑ ℓ ∈ S, ∑ m ∈ S, (a ℓ m)⁻¹ := by
    refine Finset.sum_pos (fun ℓ _ => Finset.sum_pos (fun m _ => inv_pos.2 (ha ℓ m)) ?_) ?_
    · exact ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
    · exact ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  refine ⟨∑ ℓ ∈ S, ∑ m ∈ S, |C ℓ m|, ∑ ℓ ∈ S, ∑ m ∈ S, k ℓ m,
    min 1 (∑ ℓ ∈ S, ∑ m ∈ S, (a ℓ m)⁻¹)⁻¹, ?_, lt_min one_pos (inv_pos.2 hpos),
    min_le_left _ _, ?_⟩
  · exact Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun m _ => abs_nonneg _
  intro ℓ m hℓ hm
  have hℓS : ℓ ∈ S := Finset.mem_range.2 (Nat.lt_succ_of_le hℓ)
  have hmS : m ∈ S := Finset.mem_range.2 (Nat.lt_succ_of_le hm)
  refine hmono ℓ m (C ℓ m) _ (k ℓ m) _ (a ℓ m) _ ?_ ?_ ?_ ?_ (min_le_left _ _)
    (lt_min one_pos (inv_pos.2 hpos)) (hP ℓ m)
  · calc C ℓ m ≤ |C ℓ m| := le_abs_self _
      _ ≤ ∑ m' ∈ S, |C ℓ m'| :=
          Finset.single_le_sum (f := fun m' => |C ℓ m'|) (fun _ _ => abs_nonneg _) hmS
      _ ≤ ∑ ℓ' ∈ S, ∑ m' ∈ S, |C ℓ' m'| :=
          Finset.single_le_sum (f := fun ℓ' => ∑ m' ∈ S, |C ℓ' m'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hℓS
  · exact Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun m _ => abs_nonneg _
  · calc k ℓ m ≤ ∑ m' ∈ S, k ℓ m' :=
          Finset.single_le_sum (f := fun m' => k ℓ m') (fun _ _ => Nat.zero_le _) hmS
      _ ≤ ∑ ℓ' ∈ S, ∑ m' ∈ S, k ℓ' m' :=
          Finset.single_le_sum (f := fun ℓ' => ∑ m' ∈ S, k ℓ' m')
            (fun _ _ => Nat.zero_le _) hℓS
  · have h1 : (a ℓ m)⁻¹ ≤ ∑ ℓ' ∈ S, ∑ m' ∈ S, (a ℓ' m')⁻¹ := by
      calc (a ℓ m)⁻¹ ≤ ∑ m' ∈ S, (a ℓ m')⁻¹ :=
            Finset.single_le_sum (f := fun m' => (a ℓ m')⁻¹)
              (fun _ _ => (inv_pos.2 (ha _ _)).le) hmS
        _ ≤ ∑ ℓ' ∈ S, ∑ m' ∈ S, (a ℓ' m')⁻¹ :=
            Finset.single_le_sum (f := fun ℓ' => ∑ m' ∈ S, (a ℓ' m')⁻¹)
              (fun _ _ => Finset.sum_nonneg fun _ _ => (inv_pos.2 (ha _ _)).le) hℓS
    have h2 : (∑ ℓ' ∈ S, ∑ m' ∈ S, (a ℓ' m')⁻¹)⁻¹ ≤ a ℓ m := by
      have := inv_anti₀ (inv_pos.2 (ha ℓ m)) h1
      rwa [inv_inv] at this
    exact (min_le_right _ _).trans h2

/-- **`TMPt` from the three weighted dilation bounds** (source 5464-5465, 5477-5482): along the
sequence the levels are eventually actual (BUC train), `ν_n → 0` and `ν_n ≤ 1`; the weight is the
sum over `j ≤ 4` of the three weighted dilation jets, so `𝔴_4 ≤ 5(|C₁|+|C₂|+|C₃|)ν^{-(k₁+k₂+k₃)}`. -/
theorem tmPt_of (D : SeqData) {dm dp : ℝ} (hv : WDil trainFv) (hp : WDil trainFp)
    (hψ : WDil trainFpsi) : TMPt D dm dp := by
  intro hst
  obtain ⟨C1, k1, a1, ha1, H1⟩ := hv
  obtain ⟨C2, k2, a2, ha2, H2⟩ := hp
  obtain ⟨C3, k3, a3, ha3, H3⟩ := hψ
  refine ⟨5 * (|C1| + |C2| + |C3|), k1 + k2 + k3, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < min a1 (min a2 a3) :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (lt_min ha1 (lt_min ha2 ha3)))
  filter_upwards [hst.actual, hsmall,
    retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne] with n hact hsm hle
  intro p hp0 hp1
  have hbuc : UnforcedLeray.Short.PartI.IsBUCTrain (D.level n).train := hact.regime.train_buc
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1 : (D.level n).ν ≤ 1 := hle.1
  have hx : (1 : ℝ) ≤ (D.level n).ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hνa1 : (D.level n).ν ≤ a1 := (lt_of_lt_of_le hsm (min_le_left _ _)).le
  have hνa2 : (D.level n).ν ≤ a2 :=
    (lt_of_lt_of_le hsm ((min_le_right _ _).trans (min_le_left _ _))).le
  have hνa3 : (D.level n).ν ≤ a3 :=
    (lt_of_lt_of_le hsm ((min_le_right _ _).trans (min_le_right _ _))).le
  have mono : ∀ (C : ℝ) (k : ℕ), k ≤ k1 + k2 + k3 →
      C * (D.level n).ν⁻¹ ^ k ≤ |C| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) := by
    intro C k hk
    calc C * (D.level n).ν⁻¹ ^ k ≤ |C| * (D.level n).ν⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hk) (abs_nonneg C)
  unfold trainWeight
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range 5, (1 + |p.2.2|) ^ 4 *
      (‖iteratedFDeriv ℝ j (trainFv (D.level n)) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFp (D.level n)) (Real.log p.1, p.2)‖ +
        ‖iteratedFDeriv ℝ j (trainFpsi (D.level n)) (Real.log p.1, p.2)‖) ≤
      (|C1| + |C2| + |C3|) * (D.level n).ν⁻¹ ^ (k1 + k2 + k3) := by
    intro j hj
    have hj5 : j < 5 := Finset.mem_range.1 hj
    have e1 := (H1 (D.level n) hbuc hνa1 j hj5 p hp0 hp1).trans (mono C1 k1 (by omega))
    have e2 := (H2 (D.level n) hbuc hνa2 j hj5 p hp0 hp1).trans (mono C2 k2 (by omega))
    have e3 := (H3 (D.level n) hbuc hνa3 j hj5 p hp0 hp1).trans (mono C3 k3 (by omega))
    rw [mul_add, mul_add]
    have := add_le_add (add_le_add e1 e2) e3
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
