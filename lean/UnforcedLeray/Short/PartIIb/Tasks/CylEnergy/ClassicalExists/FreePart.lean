import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatGrad
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCommute
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatWBounds
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatEqn

/-!


Proves `FreePart` (`Sub/T22_1/Stages.lean`, with `0 < c`). Source of record
`the November 2 reference manuscript`, lines 2074-2093 and 2103-2105. The proof
uses the heat toolbox tasks `T22/1/4` (`heatWBounds`), `/5` (`heatPeriodic`), `/6`
(`heatGradFormula`), `/7` (`heatCommute`), `/8` (`heatEqn`), `/9` (`heatCont`) and the
Gaussian moments `/3` (`heatKernelMoments`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

namespace CylPDE

namespace FP

lemma wb_mono {B B' : ℝ} {g : Pl → ℝ} (hBB : B ≤ B') (hg : WB B g) : WB B' g :=
  fun x => (hg x).trans hBB

/-- A cylinder test function (with `0 < c`) is bounded in the weight `cosh η`. -/
lemma wb_cyl {c : ℝ} (hc : 0 < c) {φ : Pl → ℝ} (hφ : B0579.IsCylTest c φ) :
    ∃ B : ℝ, 0 ≤ B ∧ WB B φ := by
  obtain ⟨R, hR⟩ := hφ.band
  have hK : IsCompact (Icc (0 : ℝ) c ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨|C| * Real.cosh R, mul_nonneg (abs_nonneg _) ((Real.cosh_pos _).le), fun x => ?_⟩
  by_cases hx : R < |x.2|
  · rw [hR x hx, abs_zero, zero_mul]
    exact mul_nonneg (abs_nonneg _) ((Real.cosh_pos _).le)
  · push_neg at hx
    have hper : Function.Periodic (fun q : ℝ => φ (q, x.2)) c := fun q => hφ.periodic (q, x.2)
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hc x.1
    have hmem : (y, x.2) ∈ Icc (0 : ℝ) c ×ˢ Icc (-R) R :=
      ⟨⟨hy.1, hy.2.le⟩, abs_le.mp hx⟩
    have h1 : |φ x| ≤ |C| := by
      have hφx : φ x = φ (y, x.2) := hxy
      rw [hφx]
      have := hC (y, x.2) hmem
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self C)
    have h2 : Real.cosh x.2 ≤ Real.cosh R := Real.cosh_le_cosh.mpr (hx.trans (le_abs_self R))
    exact mul_le_mul h1 h2 ((Real.cosh_pos _).le) (abs_nonneg _)

lemma heatSG_of_nonpos {a : ℝ} (ha : a ≤ 0) (g : Pl → ℝ) : heatSG a g = g := by
  funext x
  simp [heatSG, ha]

lemma heatK_cont (a : ℝ) : Continuous (heatK a) := by
  unfold heatK
  fun_prop

/-- Linearity of the semigroup on weighted-bounded continuous functions. -/
lemma heatSG_add {a B : ℝ} {g h : Pl → ℝ} (hg : Continuous g) (hgW : WB B g)
    (hh : Continuous h) (hhW : WB B h) (x : Pl) :
    heatSG a (fun y => g y + h y) x = heatSG a g x + heatSG a h x := by
  by_cases ha : a ≤ 0
  · simp [heatSG, ha]
  · have ha' : 0 < a := lt_of_not_ge ha
    have hKM := heatKernelMoments a ha'
    have hpos : ∀ y : Pl, 0 < heatK a (x - y) := fun y => hKM.1 (x - y)
    have hKi : Integrable (fun y : Pl => heatK a (x - y)) := hKM.2.1.comp_sub_left x
    have hkb : ∀ k : Pl → ℝ, WB B k → ∀ y : Pl, |k y| ≤ B := fun k hkW y =>
      (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_cosh _)).trans (hkW y)
    have hint : ∀ k : Pl → ℝ, Continuous k → WB B k →
        Integrable (fun y : Pl => heatK a (x - y) * k y) := by
      intro k hk hkW
      refine Integrable.mono' (hKi.const_mul B) ?_ ?_
      · exact (((heatK_cont a).comp (continuous_const.sub continuous_id)).mul hk).aestronglyMeasurable
      · refine Eventually.of_forall fun y => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos y)]
        calc heatK a (x - y) * |k y| ≤ heatK a (x - y) * B :=
              mul_le_mul_of_nonneg_left (hkb k hkW y) (hpos y).le
          _ = B * heatK a (x - y) := mul_comm _ _
    have hA := hint g hg hgW
    have hB := hint h hh hhW
    simp only [heatSG, if_neg ha]
    rw [← integral_add hA hB]
    congr 1
    funext y
    ring

lemma fderiv_apply_pl (G : Pl → ℝ) (x v : Pl) :
    fderiv ℝ G x v = v.1 * B0579.pd 0 G x + v.2 * B0579.pd 1 G x := by
  have hv : v = v.1 • B0579.dir 0 + v.2 • B0579.dir 1 := by
    ext <;> simp [B0579.dir]
  have e0 : B0579.pd 0 G x = fderiv ℝ G x (B0579.dir 0) := rfl
  have e1 : B0579.pd 1 G x = fderiv ℝ G x (B0579.dir 1) := rfl
  rw [e0, e1]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The semigroup at a fixed positive time is `C¹`. -/
lemma contDiff_one_heatSG {a B : ℝ} (ha : 0 < a) {g : Pl → ℝ} (hg : Continuous g)
    (hW : WB B g) : ContDiff ℝ 1 (heatSG a g) := by
  obtain ⟨hd, hpd, hcont⟩ := heatGradFormula B g hg hW a ha
  rw [contDiff_one_iff_fderiv]
  refine ⟨hd, ?_⟩
  have hfd : fderiv ℝ (heatSG a g) = fun x =>
      heatSGd 0 a g x • ContinuousLinearMap.fst ℝ ℝ ℝ + heatSGd 1 a g x • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_apply_pl]
    simp [hpd, mul_comm]
  rw [hfd]
  exact ((hcont 0).smul continuous_const).add ((hcont 1).smul continuous_const)

/-- The semigroup at a fixed positive time is `C²` for a continuous weighted-bounded function
with weighted-bounded continuous first derivatives. -/
lemma contDiff_two_heatSG {B a : ℝ} (ha : 0 < a) {f : Pl → ℝ} (hfc : Continuous f)
    (hf1 : ContDiff ℝ 1 f) (hW : WB B f) (hWj : ∀ j : Fin 2, WB B (B0579.pd j f))
    (hpc : ∀ j : Fin 2, Continuous (B0579.pd j f)) :
    ContDiff ℝ 2 (heatSG a f) := by
  obtain ⟨hd, -, -⟩ := heatGradFormula B f hfc hW a ha
  have hc0 : ∀ (j : Fin 2) (x : Pl), B0579.pd j (heatSG a f) x = heatSG a (B0579.pd j f) x :=
    fun j x => heatCommute B f hf1 hW hWj a j x
  have hfd : fderiv ℝ (heatSG a f) = fun x =>
      heatSG a (B0579.pd 0 f) x • ContinuousLinearMap.fst ℝ ℝ ℝ +
        heatSG a (B0579.pd 1 f) x • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_apply_pl, hc0 0 x, hc0 1 x]
    simp [mul_comm]
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨hd, fun h => absurd h (by simp), ?_⟩
  rw [hfd]
  exact ((contDiff_one_heatSG ha (hpc 0) (hWj 0)).smul contDiff_const).add
    ((contDiff_one_heatSG ha (hpc 1) (hWj 1)).smul contDiff_const)

end FP

theorem freePart : UnforcedLeray.Short.IIb.CylPDE.FreePart := by
  intro c ν s T f hc hν hst hf
  have hf2 : ContDiff ℝ 2 f := hf.smooth.of_le (by simp)
  have hf1 : ContDiff ℝ 1 f := hf.smooth.of_le (by simp)
  have hfc : Continuous f := hf.continuous
  have hpc : ∀ j : Fin 2, Continuous (B0579.pd j f) := fun j => (hf.pd j).continuous
  have hpc2 : ∀ i j : Fin 2, Continuous (B0579.pd i (B0579.pd j f)) :=
    fun i j => ((hf.pd j).pd i).continuous
  have hpd1 : ∀ j : Fin 2, ContDiff ℝ 1 (B0579.pd j f) :=
    fun j => ((hf.pd j).smooth).of_le (by simp)
  obtain ⟨B, hB0, hBf, hBj, hBjj⟩ : ∃ B : ℝ, 0 ≤ B ∧ WB B f ∧
      (∀ j : Fin 2, WB B (B0579.pd j f)) ∧
      (∀ i j : Fin 2, WB B (B0579.pd i (B0579.pd j f))) := by
    obtain ⟨Bf, hBf0, hBfw⟩ := FP.wb_cyl hc hf
    obtain ⟨B0, hB0', hB0w⟩ := FP.wb_cyl hc (hf.pd 0)
    obtain ⟨B1, hB1', hB1w⟩ := FP.wb_cyl hc (hf.pd 1)
    obtain ⟨C00, hC00', hC00w⟩ := FP.wb_cyl hc ((hf.pd 0).pd 0)
    obtain ⟨C01, hC01', hC01w⟩ := FP.wb_cyl hc ((hf.pd 1).pd 0)
    obtain ⟨C10, hC10', hC10w⟩ := FP.wb_cyl hc ((hf.pd 0).pd 1)
    obtain ⟨C11, hC11', hC11w⟩ := FP.wb_cyl hc ((hf.pd 1).pd 1)
    refine ⟨Bf + B0 + B1 + C00 + C01 + C10 + C11, by linarith, FP.wb_mono (by linarith) hBfw,
      ?_, ?_⟩
    · intro j
      fin_cases j
      · exact FP.wb_mono (by linarith) hB0w
      · exact FP.wb_mono (by linarith) hB1w
    · intro i j
      fin_cases i <;> fin_cases j
      · exact FP.wb_mono (by linarith) hC00w
      · exact FP.wb_mono (by linarith) hC01w
      · exact FP.wb_mono (by linarith) hC10w
      · exact FP.wb_mono (by linarith) hC11w
  have hcomm : ∀ (a : ℝ) (j : Fin 2) (x : Pl),
      B0579.pd j (heatSG a f) x = heatSG a (B0579.pd j f) x :=
    fun a j x => heatCommute B f hf1 hBf hBj a j x
  have hcomm2 : ∀ (a : ℝ) (i j : Fin 2) (x : Pl),
      B0579.pd i (B0579.pd j (heatSG a f)) x = heatSG a (B0579.pd i (B0579.pd j f)) x := by
    intro a i j x
    have e : B0579.pd j (heatSG a f) = heatSG a (B0579.pd j f) := funext (hcomm a j)
    rw [e]
    exact heatCommute B (B0579.pd j f) (hpd1 j) (hBj j) (fun i' => hBjj i' j) a i x
  have hkey : ∀ (a : ℝ) (x : Pl), lapP (heatSG a f) x = heatSG a (lapP f) x := by
    intro a x
    simp only [lapP]
    rw [hcomm2 a 0 0 x, hcomm2 a 1 1 x]
    exact (FP.heatSG_add (hpc2 0 0) (hBjj 0 0) (hpc2 1 1) (hBjj 1 1) x).symm
  -- joint continuity in (σ, x) for a weighted-bounded continuous function
  have hcontOn : ∀ g : Pl → ℝ, Continuous g → WB B g →
      ContinuousOn (fun z : ℝ × Pl => heatSG (ν * (z.1 - s)) g z.2) (Icc s T ×ˢ univ) := by
    intro g hg hgW
    have hHC := heatCont B g hg hgW
    have hmap : ContinuousOn (fun z : ℝ × Pl => (ν * (z.1 - s), z.2)) (Icc s T ×ˢ univ) :=
      (Continuous.prodMk (continuous_const.mul (continuous_fst.sub continuous_const))
        continuous_snd).continuousOn
    refine hHC.comp hmap ?_
    intro z hz
    exact ⟨mul_nonneg hν.le (sub_nonneg.mpr hz.1.1), trivial⟩
  -- the conjunct (1): C² slices
  have c1 : ∀ σ ∈ Icc s T, ContDiff ℝ 2 (heatSG (ν * (σ - s)) f) := by
    intro σ hσ
    rcases eq_or_lt_of_le (mul_nonneg hν.le (sub_nonneg.mpr hσ.1) :
        (0 : ℝ) ≤ ν * (σ - s)) with h0 | h0
    · rw [← h0, FP.heatSG_of_nonpos (le_refl (0 : ℝ)) f]
      exact hf2
    · exact FP.contDiff_two_heatSG h0 hfc hf1 hBf hBj hpc
  have c6 : ∀ j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd j (heatSG (ν * (z.1 - s)) f) z.2) (Icc s T ×ˢ univ) := by
    intro j
    have e : (fun z : ℝ × Pl => B0579.pd j (heatSG (ν * (z.1 - s)) f) z.2) =
        fun z : ℝ × Pl => heatSG (ν * (z.1 - s)) (B0579.pd j f) z.2 := by
      funext z
      exact hcomm _ j z.2
    rw [e]
    exact hcontOn _ (hpc j) (hBj j)
  have c7 : ∀ i j : Fin 2, ContinuousOn
      (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (heatSG (ν * (z.1 - s)) f)) z.2)
      (Icc s T ×ˢ univ) := by
    intro i j
    have e : (fun z : ℝ × Pl => B0579.pd i (B0579.pd j (heatSG (ν * (z.1 - s)) f)) z.2) =
        fun z : ℝ × Pl => heatSG (ν * (z.1 - s)) (B0579.pd i (B0579.pd j f)) z.2 := by
      funext z
      exact hcomm2 _ i j z.2
    rw [e]
    exact hcontOn _ (hpc2 i j) (hBjj i j)
  -- the weighted bound of the semigroup
  have hbnd : ∀ σ ∈ Icc s T, ∀ g : Pl → ℝ, WB B g → ∀ x : Pl,
      |heatSG (ν * (σ - s)) g x| * Real.cosh x.2 ≤ 2 * Real.exp (ν * (T - s)) * B := by
    intro σ hσ g hg x
    have ha0 : 0 ≤ ν * (σ - s) := mul_nonneg hν.le (sub_nonneg.mpr hσ.1)
    have hle : Real.exp (ν * (σ - s)) ≤ Real.exp (ν * (T - s)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hσ.2]) hν.le)
    have hW := (heatWBounds B g hg).1 _ ha0 x
    calc |heatSG (ν * (σ - s)) g x| * Real.cosh x.2
        ≤ 2 * Real.exp (ν * (σ - s)) * B := hW
      _ ≤ 2 * Real.exp (ν * (T - s)) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by norm_num)) hB0
  have c8 : ∃ K : ℝ, ∀ σ ∈ Icc s T, ∀ x : Pl,
      W2 (heatSG (ν * (σ - s)) f) x * Real.cosh x.2 ≤ K := by
    refine ⟨7 * (2 * Real.exp (ν * (T - s)) * B), fun σ hσ x => ?_⟩
    unfold W2
    simp only [hcomm2, hcomm]
    simp only [add_mul]
    have e1 := hbnd σ hσ f hBf x
    have e2 := hbnd σ hσ _ (hBj 0) x
    have e3 := hbnd σ hσ _ (hBj 1) x
    have e4 := hbnd σ hσ _ (hBjj 0 0) x
    have e5 := hbnd σ hσ _ (hBjj 0 1) x
    have e6 := hbnd σ hσ _ (hBjj 1 0) x
    have e7 := hbnd σ hσ _ (hBjj 1 1) x
    linarith
  -- the heat equation in the time variable
  have c9 : ∀ σ ∈ Icc s T, ∀ x : Pl, HasDerivWithinAt (fun t => heatSG (ν * (t - s)) f x)
      (ν * lapP (heatSG (ν * (σ - s)) f) x) (Icc s T) σ := by
    intro σ hσ x
    obtain ⟨hE1, hE2⟩ := heatEqn B f hf2 hBf hBj hBjj x
    have hl0 : HasDerivWithinAt (fun t => ν * (t - s)) ν (Icc s T) s := by
      have := ((hasDerivAt_id s).sub_const s).const_mul ν
      simpa using this.hasDerivWithinAt
    rcases eq_or_lt_of_le hσ.1 with h0 | h0
    · rw [← h0, sub_self, mul_zero, FP.heatSG_of_nonpos (le_refl (0 : ℝ)) f]
      have hE2' : HasDerivWithinAt (fun b => heatSG b f x) (lapP f x) (Ici 0)
          (ν * (s - s)) := by
        rw [sub_self, mul_zero]
        exact hE2
      have hmaps : MapsTo (fun t => ν * (t - s)) (Icc s T) (Ici 0) :=
        fun t ht => mul_nonneg hν.le (sub_nonneg.mpr ht.1)
      have hcomp := hE2'.comp s hl0 hmaps
      exact hcomp.congr_deriv (mul_comm _ _)
    · have ha : 0 < ν * (σ - s) := mul_pos hν (sub_pos.mpr h0)
      have hD := hE1 _ ha
      have hl : HasDerivAt (fun t => ν * (t - s)) ν σ := by
        simpa using ((hasDerivAt_id σ).sub_const s).const_mul ν
      have hc' := hD.comp σ hl
      refine (hc'.hasDerivWithinAt).congr_deriv ?_
      rw [hkey]
      ring
  refine ⟨c1, fun σ _ x => (heatPeriodic c f hf.periodic (ν * (σ - s)) x).1, ?_, ?_,
    hcontOn f hfc hBf, c6, c7, c8, c9⟩
  · intro σ _ j x
    exact hcomm _ j x
  · intro σ _ i j x
    exact hcomm2 _ i j x

end CylPDE

end UnforcedLeray.Short.IIb
