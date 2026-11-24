import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ChartLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1.RawSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.C
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.MeanJetsFixed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingProfileMeridJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.RawStreamProfile

/-!
# `PartIII-b:C/ward/12/3/2/2/2/4` helper: `RawFarJets3` from Part I fixed-parameter train bounds

Source `the November 2 reference manuscript`
lines 1206-1222 (`b_raw = (v₁, v₂ + εH)` equals `ringStreamProfile R Ψ`, homogeneous lift `N_v`),
397-404 and 427-446 (fixed-parameter velocity and stream fluctuation jets), 2542-2546 (far-field
homogeneity).

Proves `rawFarJets3_of` from the two pending Part I fixed-parameter statements
`PartI.TrainJetsBoundedFixed` (`PartI:HF/1`) and `PartI.TrainFluctAgeJetFixed` (`PartI:HF/2`),
via `meanJetsFixed_of`, `zeroFromGrad`, `jointFromAgeJets`, `rawStreamProfile`,
`ringProfileMeridJet`, `rawProfSmoothGen`, and `chartLiftJets`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Cyl (Plane)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Order-3 far-field jets of the raw field, homogeneity `-1`**
(source `the November 2 reference manuscript`
lines 1206-1222, 2542-2546; order-3 analogue of `RawFarJets`, `FarOrg.lean:173`): `raw` is jointly
`C^∞` on the far region and `‖D^k raw(τ)(y)‖ ≤ C ϱ^{-1-k}(1+|y₃|/ϱ)^M` for `k ≤ 3`, `ϱ > R₀`,
every `τ`. -/
def RawFarJets3 : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ (C R0 : ℝ) (M : ℕ), 0 < R0 ∧
        ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)
          {x : ℝ × UnforcedLeray.Space | R0 < Axi.ϱ x.2} ∧
        ∀ (τ : ℝ) (y : UnforcedLeray.Space), R0 < Axi.ϱ y → ∀ k : ℕ, k ≤ 3 →
          ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤
            C * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ M)

/-- **Order-3 chart jets of the raw profile near age zero** (source lines 1206-1222, 397-404,
427-446; order-3 analogue of `RawProfFarJet`, `FarOrg.lean:161`): `b_raw` is `C^∞` on `s > 0` and
its jets of order `l ≤ 3` are `≤ C(1+|η|)^M` on `0 < s ≤ s₀`. -/
def RawProfFarJet3 : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
          {m : ℝ × (ℝ × ℝ) | 0 < m.1} ∧
      ∃ (C s0 : ℝ) (M : ℕ), 0 < s0 ∧ ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ s0 → ∀ l ≤ 3,
        ‖iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) m‖ ≤
          C * (1 + |m.2.2|) ^ M

namespace RawFar3Aux

/-- Coordinate projection `(s, (q, η)) ↦ (s, η)` has operator norm at most `1`. -/
private def Lproj : (ℝ × Plane) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ Plane).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Plane))

private lemma Lproj_apply (x : ℝ × Plane) : Lproj x = (x.1, x.2.2) := rfl

private lemma norm_Lproj_le_one : ‖Lproj‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [Lproj_apply, one_mul, Prod.norm_def, Prod.norm_def]
  simp only [Prod.norm_def]
  exact max_le (le_max_left _ _) ((le_max_right _ _).trans' (le_max_right _ _))

/-- Pullback of a derivative bound along `Lproj (s, (q, η)) = (s, η)` on `s > 0`. -/
private lemma norm_iteratedFDeriv_comp_Lproj (Φ : ℝ × ℝ → ℝ)
    (hΦ : ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ)) (i : ℕ) {M : ℝ}
    (hΦb : ∀ z : ℝ × ℝ, 0 < z.1 → ‖iteratedFDeriv ℝ i Φ z‖ ≤ M)
    {y : ℝ × Plane} (hy : 0 < y.1) :
    ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => Φ (x.1, x.2.2)) y‖ ≤ M := by
  set U : Set (ℝ × Plane) := Ioi 0 ×ˢ univ
  set U2 : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ
  have hUo : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hU2o : IsOpen U2 := isOpen_Ioi.prod isOpen_univ
  have hpre : Lproj ⁻¹' U2 = U := by
    ext x
    simp [Lproj_apply, U, U2]
  have hyU : y ∈ U := ⟨hy, mem_univ _⟩
  have hyU2 : Lproj y ∈ U2 := ⟨hy, mem_univ _⟩
  have hfun : (fun x : ℝ × Plane => Φ (x.1, x.2.2)) = Φ ∘ Lproj := rfl
  have hcomp := Lproj.iteratedFDerivWithin_comp_right hΦ hU2o.uniqueDiffOn
    (hpre ▸ hUo.uniqueDiffOn) hyU2 (i := i) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_of_isOpen i hUo hyU,
    iteratedFDerivWithin_of_isOpen i hU2o hyU2] at hcomp
  rw [hfun, hcomp]
  have h1 : ∏ _j : Fin i, ‖Lproj‖ ≤ 1 := by
    rw [Finset.prod_const]
    exact pow_le_one₀ (norm_nonneg _) norm_Lproj_le_one
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i Φ (Lproj y)) (fun _ => Lproj)
  have h3 := hΦb (Lproj y) hy
  calc ‖(iteratedFDeriv ℝ i Φ (Lproj y)).compContinuousLinearMap (fun _ => Lproj)‖
      ≤ ‖iteratedFDeriv ℝ i Φ (Lproj y)‖ * ∏ _j : Fin i, ‖Lproj‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ i Φ (Lproj y)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ M := by rw [mul_one]; exact h3

/-- Order-`≤ 4` joint jets of `(s, (q, η)) ↦ meanStream tr s η` on `0 < s ≤ 1` from
`MeanJetsFixed` and `zeroFromGrad`. -/
private lemma meanStream_jets4_of (hJ : MeanJetsFixed) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
          (Ioi 0 ×ˢ univ) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, l ≤ 4 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 →
          ‖iteratedFDeriv ℝ l
            (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤
              C * (1 + |y.2.2|) := by
  obtain ⟨ν₀, hν₀, HJ⟩ := hJ 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν c hν hν₀' hc tr hbuc => ?_⟩
  have hcp : c = UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg hν.le, Real.rpow_two]
  have hc0 : 0 < c := by rw [hc]; positivity
  have hsm2 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν c hν hc0 tr hbuc
  have hsm : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ) :=
    hsm2.comp Lproj.contDiff.contDiffOn (fun x hx => ⟨hx.1, mem_univ _⟩)
  refine ⟨hsm, ?_⟩
  obtain ⟨M1, hM1⟩ := HJ ν c hν hν₀' hcp tr hbuc 1 (by omega)
  obtain ⟨M2, hM2⟩ := HJ ν c hν hν₀' hcp tr hbuc 2 (by omega)
  obtain ⟨M3, hM3⟩ := HJ ν c hν hν₀' hcp tr hbuc 3 (by omega)
  obtain ⟨M4, hM4⟩ := HJ ν c hν hν₀' hcp tr hbuc 4 (by omega)
  set B : ℝ := max (max (max M1 M2) (max M3 M4)) 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hM1B : M1 ≤ B :=
    (le_max_left M1 M2).trans ((le_max_left _ _).trans (le_max_left _ 0))
  have hM2B : M2 ≤ B :=
    (le_max_right M1 M2).trans ((le_max_left _ _).trans (le_max_left _ 0))
  have hM3B : M3 ≤ B :=
    (le_max_left M3 M4).trans ((le_max_right _ _).trans (le_max_left _ 0))
  have hM4B : M4 ≤ B :=
    (le_max_right M3 M4).trans ((le_max_right _ _).trans (le_max_left _ 0))
  have hbpos : ∀ l : ℕ, 1 ≤ l → l ≤ 4 → ∀ y : ℝ × Plane, 0 < y.1 →
      ‖iteratedFDeriv ℝ l
        (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ B := by
    intro l hl1 hl4 y hy
    interval_cases l
    · exact norm_iteratedFDeriv_comp_Lproj _ hsm2 1
        (fun z hz => (hM1 z hz).trans hM1B) hy
    · exact norm_iteratedFDeriv_comp_Lproj _ hsm2 2
        (fun z hz => (hM2 z hz).trans hM2B) hy
    · exact norm_iteratedFDeriv_comp_Lproj _ hsm2 3
        (fun z hz => (hM3 z hz).trans hM3B) hy
    · exact norm_iteratedFDeriv_comp_Lproj _ hsm2 4
        (fun z hz => (hM4 z hz).trans hM4B) hy
  have h0 := zeroFromGrad (UnforcedLeray.Short.PartI.meanStream tr) B hsm2
    (fun y hy => hbpos 1 le_rfl (by omega) y hy) 1 one_pos
  set K : ℝ := |UnforcedLeray.Short.PartI.meanStream tr 1 0| + B
  refine ⟨K, by positivity, fun l hl y hy hy1 => ?_⟩
  have hη : 0 ≤ |y.2.2| := abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  rcases Nat.eq_zero_or_pos l with rfl | hlpos
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have h0y := h0 y hy hy1
    nlinarith [abs_nonneg (UnforcedLeray.Short.PartI.meanStream tr 1 0), mul_nonneg hB0 hη]
  · have hly := hbpos l hlpos hl y hy
    have hBK : B ≤ K := by
      dsimp [K]
      linarith [abs_nonneg (UnforcedLeray.Short.PartI.meanStream tr 1 0)]
    nlinarith [mul_nonneg hK0 hη]

/-- Order-`≤ 4` joint jets of the stream fluctuation `ψ - meanStream` on `s > 0` from
`PartI.TrainFluctAgeJetFixed` and `PartI.jointFromAgeJets`. -/
private lemma fluct_jets4_of (hF : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, l ≤ 4 → ∀ y : ℝ × Plane, 0 < y.1 →
          ‖iteratedFDeriv ℝ l
            (fun x : ℝ × Plane =>
              tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖ ≤ C := by
  obtain ⟨ν₀, hν₀, HF⟩ := hF 2 (by norm_num)
  refine ⟨ν₀, hν₀, fun ν c hν hν₀' hc tr hbuc => ?_⟩
  have hcp : UnforcedLeray.Short.PartI.trainPeriod 2 ν = c := by
    rw [hc, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg hν.le, Real.rpow_two]
  subst hcp
  have hc0 : 0 < UnforcedLeray.Short.PartI.trainPeriod 2 ν := by
    rw [hc]; positivity
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν hc0 tr hbuc
  have hsm2 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.bucMeanStreamSmooth ν _ hν hc0 tr hbuc
  have hsm : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ) :=
    hsm2.comp Lproj.contDiff.contDiffOn (fun x hx => ⟨hx.1, mem_univ _⟩)
  set F : ℝ → Plane → ℝ :=
    fun r w => tr.ψ r w -
      UnforcedLeray.Short.PartI.hmean (UnforcedLeray.Short.PartI.trainPeriod 2 ν) (tr.ψ r) w.2
  have hFeq :
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) =
        (fun x : ℝ × Plane => F x.1 x.2) := rfl
  have hfl : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) := by
    rw [← hFeq]
    exact hψ.sub hsm
  have hage : ∀ ℓ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖UnforcedLeray.Short.PartI.ageJet ℓ j F s z‖ ≤ B := by
    intro ℓ j
    obtain ⟨C, κ, hκ, hC⟩ := HF ν hν hν₀' tr hbuc ℓ j
    refine ⟨|C|, abs_nonneg C, fun s hs z => ?_⟩
    have he0 : 0 ≤ Real.exp (-(κ * s)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(κ * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκ.le hs.le))
    have h1 : ‖UnforcedLeray.Short.PartI.ageJet ℓ j F s z‖ ≤
        C * Real.exp (-(κ * s)) := hC s hs z
    calc _ ≤ C * Real.exp (-(κ * s)) := h1
      _ ≤ |C| * Real.exp (-(κ * s)) := mul_le_mul_of_nonneg_right (le_abs_self C) he0
      _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) he1
  choose B hB0 hB using hage
  have hJ : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℝ → Plane → ℝ,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ) →
      ∀ y : ℝ × Plane, 0 < y.1 →
        ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => G x.1 x.2) y‖ ≤
          K * ∑ ℓ ∈ Finset.range (i + 1),
            ‖UnforcedLeray.Short.PartI.ageJet ℓ (i - ℓ) G y.1 y.2‖ :=
    UnforcedLeray.Short.PartI.jointFromAgeJets
  choose K hK0 hK using hJ
  refine ⟨∑ l ∈ Finset.range 5, K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ),
    Finset.sum_nonneg (fun l _ => mul_nonneg (hK0 l) (Finset.sum_nonneg (fun ℓ _ => hB0 ℓ (l - ℓ)))),
    fun l hl y hy => ?_⟩
  have hl5 : l ∈ Finset.range 5 := Finset.mem_range.2 (by omega)
  rw [hFeq]
  calc ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => F x.1 x.2) y‖
      ≤ K l * ∑ ℓ ∈ Finset.range (l + 1),
          ‖UnforcedLeray.Short.PartI.ageJet ℓ (l - ℓ) F y.1 y.2‖ :=
        hK l F hfl y hy
    _ ≤ K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ℓ _ => hB ℓ (l - ℓ) y.1 hy y.2)) (hK0 l)
    _ ≤ ∑ l ∈ Finset.range 5, K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ) :=
        Finset.single_le_sum
          (f := fun l => K l * ∑ ℓ ∈ Finset.range (l + 1), B ℓ (l - ℓ))
          (fun l' _ => mul_nonneg (hK0 l') (Finset.sum_nonneg (fun ℓ _ => hB0 ℓ (l' - ℓ)))) hl5

/-- Order-`≤ 4` joint jets of `tr.ψ` on `0 < s ≤ 1` from `TrainJetsBoundedFixed` and
`TrainFluctAgeJetFixed`. -/
private lemma stream_jets4_of (h1 : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed)
    (h2 : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℕ, l ≤ 4 → ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 →
          ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => tr.ψ x.1 x.2) y‖ ≤
            C * (1 + |y.2.2|) := by
  obtain ⟨ν1, hν1, H1⟩ := meanStream_jets4_of (meanJetsFixed_of h1)
  obtain ⟨ν2, hν2, H2⟩ := fluct_jets4_of h2
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun ν c hν hν₀ hc tr hbuc => ?_⟩
  obtain ⟨hsm, C1, hC1, h1b⟩ := H1 ν c hν (hν₀.trans (min_le_left _ _)) hc tr hbuc
  obtain ⟨C2, hC2, h2b⟩ := H2 ν c hν (hν₀.trans (min_le_right _ _)) hc tr hbuc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hψ : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν c hν hc0 tr hbuc
  have hfl : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2)
      (Ioi 0 ×ˢ univ) := hψ.sub hsm
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  refine ⟨C1 + C2, add_nonneg hC1 hC2, fun l hl y hy hy1 => ?_⟩
  have hyU : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hy, mem_univ _⟩
  have hsmAt : ContDiffAt ℝ l
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y :=
    (hsm.contDiffAt (hUo.mem_nhds hyU)).of_le (by exact_mod_cast le_top)
  have hflAt : ContDiffAt ℝ l
      (fun x : ℝ × Plane => tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y :=
    (hfl.contDiffAt (hUo.mem_nhds hyU)).of_le (by exact_mod_cast le_top)
  have hsplit : (fun x : ℝ × Plane => tr.ψ x.1 x.2) =
      (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) +
        (fun x : ℝ × Plane => tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) := by
    funext x
    simp
  rw [hsplit, iteratedFDeriv_add_apply hsmAt hflAt]
  have b1 := h1b l hl y hy hy1
  have b2 := h2b l hl y hy
  have hη : 1 ≤ 1 + |y.2.2| := by linarith [abs_nonneg y.2.2]
  have b2' : C2 ≤ C2 * (1 + |y.2.2|) := le_mul_of_one_le_right hC2 hη
  calc ‖iteratedFDeriv ℝ l
        (fun x : ℝ × Plane => UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y +
      iteratedFDeriv ℝ l
        (fun x : ℝ × Plane => tr.ψ x.1 x.2 - UnforcedLeray.Short.PartI.meanStream tr x.1 x.2.2) y‖
      ≤ _ := norm_add_le _ _
    _ ≤ C1 * (1 + |y.2.2|) + C2 * (1 + |y.2.2|) := add_le_add b1 (b2.trans b2')
    _ = (C1 + C2) * (1 + |y.2.2|) := by ring

/-- `RawProfFarJet3` from `TrainJetsBoundedFixed` and `TrainFluctAgeJetFixed`, using
`rawStreamProfile` and `ringProfileMeridJet`. -/
theorem rawProfFarJet3_of (h1 : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed)
    (h2 : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) : RawProfFarJet3 := by
  intro dm dp _hdm
  obtain ⟨ν₀, hν₀, Hψ⟩ := stream_jets4_of h1 h2
  refine ⟨ν₀, hν₀, fun p d hreg hν => ?_⟩
  have hsm : ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
      {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    rawProfSmoothGen p.ε p.train.v p.train.ψ p.train.isTrain.smooth_v hreg.train_stream_smooth
  refine ⟨hsm, ?_⟩
  obtain ⟨Cψ, hCψ0, hCψ⟩ := Hψ p.ν p.c p.ν_pos hν hreg.c_eq p.train hreg.train_buc
  obtain ⟨_, hM⟩ := ringProfileMeridJet p.R (fun y => p.train.ψ y.1 y.2) hreg.train_stream_smooth
  obtain ⟨C0, hC0⟩ := hM 0
  obtain ⟨C1, hC1⟩ := hM 1
  obtain ⟨C2, hC2⟩ := hM 2
  obtain ⟨C3, hC3⟩ := hM 3
  set CM : ℝ := max (max (max C0 C1) (max C2 C3)) 0
  have hCM0 : 0 ≤ CM := le_max_right _ _
  have hC0M : C0 ≤ CM :=
    (le_max_left C0 C1).trans ((le_max_left _ _).trans (le_max_left _ 0))
  have hC1M : C1 ≤ CM :=
    (le_max_right C0 C1).trans ((le_max_left _ _).trans (le_max_left _ 0))
  have hC2M : C2 ≤ CM :=
    (le_max_left C2 C3).trans ((le_max_right _ _).trans (le_max_left _ 0))
  have hC3M : C3 ≤ CM :=
    (le_max_right C2 C3).trans ((le_max_right _ _).trans (le_max_left _ 0))
  have hUopen : IsOpen {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    isOpen_lt continuous_const continuous_fst
  have hRawEq : ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ y =
        UnforcedLeray.Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2) y := by
    intro y hy
    have hεR : p.R⁻¹ = p.ε := inv_inv p.ε
    rw [← hεR]
    exact UnforcedLeray.Short.IIb.rawStreamProfile p.ν p.c p.R p.train p.R_pos
      hreg.train_stream_smooth y hy
  refine ⟨10 * CM * Cψ, 1, 2, one_pos, fun m hm0 hms l hl => ?_⟩
  have hev : UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ =ᶠ[𝓝 m]
      UnforcedLeray.Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2) :=
    Filter.eventuallyEq_of_mem (hUopen.mem_nhds hm0) (fun z hz => hRawEq z hz)
  rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds]
  have hRing : ‖iteratedFDeriv ℝ l
      (UnforcedLeray.Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2)) m‖ ≤
        CM * (1 + |m.1| + |m.2.2|) *
          ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ := by
    have hS0 : 0 ≤ ∑ j ∈ Finset.range (l + 2),
        ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have h10 : 0 ≤ 1 + |m.1| + |m.2.2| := by positivity
    interval_cases l
    · exact (hC0 m hm0).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0M h10) hS0)
    · exact (hC1 m hm0).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1M h10) hS0)
    · exact (hC2 m hm0).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2M h10) hS0)
    · exact (hC3 m hm0).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3M h10) hS0)
  have h1m : 1 + |m.1| + |m.2.2| ≤ 2 * (1 + |m.2.2|) := by
    rw [abs_of_pos hm0]
    linarith [abs_nonneg m.2.2]
  have hsum : ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ ≤
      5 * (Cψ * (1 + |m.2.2|)) := by
    have hcard : ((l : ℝ) + 2) ≤ 5 := by
      have : (l : ℝ) ≤ 3 := by exact_mod_cast hl
      linarith
    calc ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖
        ≤ ∑ _j ∈ Finset.range (l + 2), Cψ * (1 + |m.2.2|) :=
          Finset.sum_le_sum (fun j hj => hCψ j (by have := Finset.mem_range.1 hj; omega) m hm0 hms)
      _ = ((l : ℝ) + 2) * (Cψ * (1 + |m.2.2|)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 5 * (Cψ * (1 + |m.2.2|)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hCψ0 (by positivity))
  have hstep : CM * (1 + |m.1| + |m.2.2|) *
      ∑ j ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ j (fun z => p.train.ψ z.1 z.2) m‖ ≤
        CM * (2 * (1 + |m.2.2|)) * (5 * (Cψ * (1 + |m.2.2|))) := by
    refine mul_le_mul
      (mul_le_mul_of_nonneg_left h1m hCM0) hsum
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (mul_nonneg hCM0 (by positivity))
  calc ‖iteratedFDeriv ℝ l
        (UnforcedLeray.Axi.ringStreamProfile p.R (fun z => p.train.ψ z.1 z.2)) m‖
      ≤ _ := hRing
    _ ≤ CM * (2 * (1 + |m.2.2|)) * (5 * (Cψ * (1 + |m.2.2|))) := hstep
    _ = 10 * CM * Cψ * (1 + |m.2.2|) ^ 2 := by ring

/-- Joint smoothness of `(τ, y) ↦ Axi.chart R τ y` off the axis. -/
private lemma chart_joint_contDiffOn (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.chart R z.1 z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
  have hϱ : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.ϱ z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    Axi.contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun _ hz => hz)
  have hAge : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.age R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    contDiffOn_const.div (hϱ.pow 2) (fun _ hz => pow_ne_zero 2 (Axi.ϱ_ne_zero hz))
  have hLog : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Real.log (Axi.age R z.2))
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    ContDiffOn.log hAge (fun _ hz => (Axi.age_pos hR.ne' hz).ne')
  have hPhase : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.phase R z.1 z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
    have h1 : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.1 / 2)
        {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
      (show ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.1 / 2) by fun_prop).contDiffOn
    exact h1.sub (contDiffOn_const.mul hLog)
  have hTrans : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.trans R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
    have h2 : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.2 2)
        {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
      (show ContDiff ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => R * z.2 2) by fun_prop).contDiffOn
    exact h2.div hϱ (fun _ hz => Axi.ϱ_ne_zero hz)
  exact hAge.prodMk (hPhase.prodMk hTrans)

/-- Joint smoothness of `(τ, y) ↦ Axi.Nv R b τ y` off the axis. -/
private lemma Nv_joint_contDiffOn (R : ℝ) (hR : 0 < R) (b : ℝ × (ℝ × ℝ) → Axi.Merid)
    (hb : ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1}) :
    ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => Axi.Nv R b z.1 z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} := by
  have hLF : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => liftFactor R z.2)
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    (clf_lift_contDiffOn R hR).comp contDiff_snd.contDiffOn (fun _ hz => hz)
  have hCh : ContDiffOn ℝ ∞ (fun z : ℝ × UnforcedLeray.Space => b (Axi.chart R z.1 z.2))
      {z : ℝ × UnforcedLeray.Space | z.2 ∉ Axi.axis} :=
    hb.comp (chart_joint_contDiffOn R hR) (fun _ hz => Axi.age_pos hR.ne' hz)
  have hEq : (fun z : ℝ × UnforcedLeray.Space => Axi.Nv R b z.1 z.2) =
      fun z => liftFactor R z.2 (b (Axi.chart R z.1 z.2)) :=
    funext fun z => Nv_eq_liftFactor R b z.1 z.2
  rw [hEq]
  exact hLF.clm_apply hCh

private lemma age_le_of_radius_gt {R s0 : ℝ} (hR : 0 < R) (hs0 : 0 < s0)
    {y : UnforcedLeray.Space} (hy : max R (R / Real.sqrt s0) < Axi.ϱ y) :
    R ≤ Axi.ϱ y ∧ Axi.age R y ≤ s0 := by
  have h1 : R < Axi.ϱ y := lt_of_le_of_lt (le_max_left _ _) hy
  have h2 : R / Real.sqrt s0 < Axi.ϱ y := lt_of_le_of_lt (le_max_right _ _) hy
  have hρ : 0 < Axi.ϱ y := hR.trans h1
  have hsq : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have h3 : R < Axi.ϱ y * Real.sqrt s0 := (div_lt_iff₀ hsq).1 h2
  have h4 : R ^ 2 ≤ (Axi.ϱ y * Real.sqrt s0) ^ 2 :=
    pow_le_pow_left₀ hR.le h3.le 2
  rw [mul_pow, Real.sq_sqrt hs0.le] at h4
  refine ⟨h1.le, ?_⟩
  unfold Axi.age
  exact (div_le_iff₀ (pow_pos hρ 2)).2 (by linarith)

/-- `RawFarJets3` from `RawProfFarJet3` and `chartLiftJets`. -/
theorem rawFarJets3_of_prof (hP : RawProfFarJet3) : RawFarJets3 := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, HP⟩ := hP dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν => ?_⟩
  set b : ℝ × (ℝ × ℝ) → Axi.Merid :=
    UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ
  obtain ⟨hb, Cb, s0, M, hs0, hbd⟩ := HP p d hreg hν
  have hν0 : 0 < p.ν := p.ν_pos
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.2
    have hneg : -d / p.ν < 0 := div_neg_of_neg_of_pos (by linarith [hreg.dm_pos, hreg.dm_le]) hν0
    exact hneg.le
  have hR1 : 1 ≤ p.R := (one_le_inv₀ p.ε_pos).2 hε1
  have hRpos : 0 < p.R := p.R_pos
  obtain ⟨K, hK0, hKb⟩ := chartLiftJets p.R hRpos
  set R0 : ℝ := max p.R (p.R / Real.sqrt s0) + 1
  have hR0pos : 0 < R0 := by
    have : p.R ≤ max p.R (p.R / Real.sqrt s0) := le_max_left _ _
    linarith
  have hNvJ : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => Axi.Nv p.R b x.1 x.2)
      {x : ℝ × UnforcedLeray.Space | R0 < Axi.ϱ x.2} :=
    (Nv_joint_contDiffOn p.R hRpos b hb).mono (fun x hx => by
      have hx' : R0 < Axi.ϱ x.2 := hx
      intro hax
      rw [Axi.mem_axis_iff] at hax
      linarith)
  have hRawJ : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)
      {x : ℝ × UnforcedLeray.Space | R0 < Axi.ϱ x.2} :=
    hNvJ.congr (fun x hx => by
      have hx' : R0 < Axi.ϱ x.2 := hx
      have hyax : x.2 ∉ Axi.axis := by
        intro hax
        rw [Axi.mem_axis_iff] at hax
        linarith
      exact UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis p x.1 x.2 hyax)
  set C0 : ℝ := max Cb 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  refine ⟨4 * K * C0 * p.R ^ M, R0, M + 3, hR0pos, hRawJ, fun τ y hy k hk => ?_⟩
  have hmax : max p.R (p.R / Real.sqrt s0) < Axi.ϱ y := by
    dsimp [R0] at hy
    linarith
  obtain ⟨hRy, hage⟩ := age_le_of_radius_gt hRpos hs0 hmax
  have hρ : 0 < Axi.ϱ y := lt_of_lt_of_le hRpos hRy
  have hyax : y ∉ Axi.axis := by
    intro hax
    rw [Axi.mem_axis_iff] at hax
    linarith
  have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R b τ :=
    Filter.eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyax)
      (fun z hz => UnforcedLeray.Cons.C03.Concrete.Params.raw_eq_off_axis p τ z hz)
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
  have hchart := hKb b hb τ y hRy k hk
  set t : ℝ := |y 2| / Axi.ϱ y
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) hρ.le
  have hs1 : 1 ≤ 1 + t := by linarith
  have hη : |(Axi.chart p.R τ y).2.2| = p.R * t := by
    show |Axi.trans p.R y| = p.R * (|y 2| / Axi.ϱ y)
    rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hρ, mul_div_assoc]
  have h1η : 1 + |(Axi.chart p.R τ y).2.2| ≤ p.R * (1 + t) := by
    rw [hη]
    nlinarith
  have hpowM : (1 + |(Axi.chart p.R τ y).2.2|) ^ M ≤ p.R ^ M * (1 + t) ^ M := by
    calc (1 + |(Axi.chart p.R τ y).2.2|) ^ M
        ≤ (p.R * (1 + t)) ^ M := pow_le_pow_left₀ (by positivity) h1η M
      _ = p.R ^ M * (1 + t) ^ M := mul_pow _ _ _
  have hm0 : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hRpos.ne' hyax
  have hms : (Axi.chart p.R τ y).1 ≤ s0 := hage
  have hbl : ∀ l : ℕ, l ≤ 3 →
      ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ ≤ C0 * (p.R ^ M * (1 + t) ^ M) := by
    intro l hl
    have h1 := hbd (Axi.chart p.R τ y) hm0 hms l hl
    have h2 : Cb ≤ C0 := le_max_left _ _
    calc ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖
        ≤ Cb * (1 + |(Axi.chart p.R τ y).2.2|) ^ M := h1
      _ ≤ C0 * (1 + |(Axi.chart p.R τ y).2.2|) ^ M :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ C0 * (p.R ^ M * (1 + t) ^ M) :=
          mul_le_mul_of_nonneg_left hpowM hC0
  have hsum : ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ ≤
      4 * (C0 * (p.R ^ M * (1 + t) ^ M)) := by
    have hk4 : ((k : ℝ) + 1) ≤ 4 := by
      have : (k : ℝ) ≤ 3 := by exact_mod_cast hk
      linarith
    calc ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖
        ≤ ∑ _l ∈ Finset.range (k + 1), C0 * (p.R ^ M * (1 + t) ^ M) :=
          Finset.sum_le_sum (fun l hl => hbl l (by have := Finset.mem_range.1 hl; omega))
      _ = ((k : ℝ) + 1) * (C0 * (p.R ^ M * (1 + t) ^ M)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 4 * (C0 * (p.R ^ M * (1 + t) ^ M)) :=
          mul_le_mul_of_nonneg_right hk4 (by positivity)
  have hpowk : (1 + t) ^ k * (1 + t) ^ M ≤ (1 + t) ^ (M + 3) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hs1 (by omega)
  have hpre0 : 0 ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ k :=
    mul_nonneg (mul_nonneg hK0.le (Real.rpow_nonneg hρ.le _)) (pow_nonneg (by positivity) _)
  have hpre1 : 0 ≤ 4 * K * C0 * p.R ^ M * Axi.ϱ y ^ (-(1 + (k : ℝ))) := by
    have : 0 ≤ Axi.ϱ y ^ (-(1 + (k : ℝ))) := Real.rpow_nonneg hρ.le _
    positivity
  calc ‖iteratedFDeriv ℝ k (Axi.Nv p.R b τ) y‖
      ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ k *
          ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ := hchart
    _ ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ k *
          (4 * (C0 * (p.R ^ M * (1 + t) ^ M))) :=
        mul_le_mul_of_nonneg_left hsum hpre0
    _ = 4 * K * C0 * p.R ^ M * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
          ((1 + t) ^ k * (1 + t) ^ M) := by ring
    _ ≤ 4 * K * C0 * p.R ^ M * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ (M + 3) :=
        mul_le_mul_of_nonneg_left hpowk hpre1
    _ = 4 * K * C0 * p.R ^ M * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + t) ^ (M + 3)) := by ring

end RawFar3Aux

/-- **`RawFarJets3` from the Part I fixed-parameter train theorems**
(`TrainJetsBoundedFixed`, task `PartI:HF/1`, and `TrainFluctAgeJetFixed`, task `PartI:HF/2`). -/
theorem rawFarJets3_of (h1 : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed)
    (h2 : UnforcedLeray.Short.PartI.TrainFluctAgeJetFixed) : RawFarJets3 :=
  RawFar3Aux.rawFarJets3_of_prof (RawFar3Aux.rawProfFarJet3_of h1 h2)

end UnforcedLeray.Short.PartIIIb.Concrete
