import UnforcedLeray.Short.PartIIb.Tasks.CylExistence
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.Periodize

/-!
# Energy bounds for free cylinder flows from cylinder tests (helper for `relB4loc_leaf`)

Source: `the November 2 reference manuscript` lines 2092-2118 (free cylinder energy)
and 2960-2970 (continuity of the free cylinder flow in the start age, by restart, linearity and
uniqueness).  For a BUC train the `X_{m,c}` energy of a regular cylinder flow grows at most like
`exp(2K(t-s))` on `[0, T]` (the Gronwall argument of `PartII-b:T23/2`, reproduced here because the
original lemma is private); weak flows from cylinder tests agree with the regular ones, so the
difference of two weak flows is controlled by the gap of their data at the later start age.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa.RelB4locAux

theorem pd_sub_eq' {f g : B0579.Plane → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun y => f y - g y) x = B0579.pd j f x - B0579.pd j g x := by
  have h := congrFun
    (mp_pd_sub (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)) 0 j) x
  simpa only [sub_zero] using h

theorem lapP_sub_eq' {f g : B0579.Plane → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : B0579.Plane) :
    lapP (fun y => f y - g y) x = lapP f x - lapP g x := by
  have h := mp_lapP_sub hf hg 0 x
  simpa only [sub_zero] using h

theorem cylSmoothDecay_sub' {c : ℝ} {g₁ g₂ : B0579.Plane → ℝ}
    (h₁ : CylSmoothDecay c g₁) (h₂ : CylSmoothDecay c g₂) :
    CylSmoothDecay c (fun x => g₁ x - g₂ x) where
  smooth := h₁.smooth.sub h₂.smooth
  periodic x := by simp only [h₁.periodic x, h₂.periodic x]
  decay N := by
    obtain ⟨C₁, hC₁⟩ := h₁.decay N
    obtain ⟨C₂, hC₂⟩ := h₂.decay N
    refine ⟨C₁ + C₂, fun x => ?_⟩
    rw [pd_sub_eq' h₁.smooth h₂.smooth 0 x, pd_sub_eq' h₁.smooth h₂.smooth 1 x,
      lapP_sub_eq' h₁.smooth h₂.smooth x]
    have hw : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have a0 : |g₁ x - g₂ x| ≤ |g₁ x| + |g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (g₁ x) (-g₂ x)
    have a1 : |B0579.pd 0 g₁ x - B0579.pd 0 g₂ x| ≤ |B0579.pd 0 g₁ x| + |B0579.pd 0 g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 0 g₁ x) (-B0579.pd 0 g₂ x)
    have a2 : |B0579.pd 1 g₁ x - B0579.pd 1 g₂ x| ≤ |B0579.pd 1 g₁ x| + |B0579.pd 1 g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 1 g₁ x) (-B0579.pd 1 g₂ x)
    have a3 : |lapP g₁ x - lapP g₂ x| ≤ |lapP g₁ x| + |lapP g₂ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (lapP g₁ x) (-lapP g₂ x)
    have hle := mul_le_mul_of_nonneg_right (by linarith :
      |g₁ x - g₂ x| + |B0579.pd 0 g₁ x - B0579.pd 0 g₂ x| +
        |B0579.pd 1 g₁ x - B0579.pd 1 g₂ x| + |lapP g₁ x - lapP g₂ x| ≤
      (|g₁ x| + |B0579.pd 0 g₁ x| + |B0579.pd 1 g₁ x| + |lapP g₁ x|) +
        (|g₂ x| + |B0579.pd 0 g₂ x| + |B0579.pd 1 g₂ x| + |lapP g₂ x|)) hw
    linarith [hC₁ x, hC₂ x]

/-- The difference of two regular cylinder flows on `[s, T]` is a regular cylinder flow. -/
theorem isRegularCylFlow_sub' {c ν s T : ℝ}
    {v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec}
    {u₁ u₂ : ℝ → B0579.Plane → ℝ}
    (hu₁ : IsRegularCylFlow c ν v s T u₁)
    (hu₂ : IsRegularCylFlow c ν v s T u₂) :
    IsRegularCylFlow c ν v s T (fun r x => u₁ r x - u₂ r x) where
  jointCont := hu₁.jointCont.sub hu₂.jointCont
  slice σ hσ := cylSmoothDecay_sub' (hu₁.slice σ hσ) (hu₂.slice σ hσ)
  decay N := by
    obtain ⟨C₁, hC₁⟩ := hu₁.decay N
    obtain ⟨C₂, hC₂⟩ := hu₂.decay N
    refine ⟨C₁ + C₂, fun σ hσ x => ?_⟩
    have s1 := (hu₁.slice σ hσ).smooth
    have s2 := (hu₂.slice σ hσ).smooth
    rw [pd_sub_eq' s1 s2 0 x, pd_sub_eq' s1 s2 1 x, lapP_sub_eq' s1 s2 x]
    have hw : 0 ≤ (1 + x.2 ^ 2) ^ N := Real.rpow_nonneg (by positivity) N
    have a0 : |u₁ σ x - u₂ σ x| ≤ |u₁ σ x| + |u₂ σ x| := by
      simpa [sub_eq_add_neg] using abs_add_le (u₁ σ x) (-u₂ σ x)
    have a1 : |B0579.pd 0 (u₁ σ) x - B0579.pd 0 (u₂ σ) x| ≤
        |B0579.pd 0 (u₁ σ) x| + |B0579.pd 0 (u₂ σ) x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 0 (u₁ σ) x) (-B0579.pd 0 (u₂ σ) x)
    have a2 : |B0579.pd 1 (u₁ σ) x - B0579.pd 1 (u₂ σ) x| ≤
        |B0579.pd 1 (u₁ σ) x| + |B0579.pd 1 (u₂ σ) x| := by
      simpa [sub_eq_add_neg] using abs_add_le (B0579.pd 1 (u₁ σ) x) (-B0579.pd 1 (u₂ σ) x)
    have a3 : |lapP (u₁ σ) x - lapP (u₂ σ) x| ≤ |lapP (u₁ σ) x| + |lapP (u₂ σ) x| := by
      simpa [sub_eq_add_neg] using abs_add_le (lapP (u₁ σ) x) (-lapP (u₂ σ) x)
    have hle := mul_le_mul_of_nonneg_right (by linarith :
      |u₁ σ x - u₂ σ x| + |B0579.pd 0 (u₁ σ) x - B0579.pd 0 (u₂ σ) x| +
        |B0579.pd 1 (u₁ σ) x - B0579.pd 1 (u₂ σ) x| + |lapP (u₁ σ) x - lapP (u₂ σ) x| ≤
      (|u₁ σ x| + |B0579.pd 0 (u₁ σ) x| + |B0579.pd 1 (u₁ σ) x| + |lapP (u₁ σ) x|) +
        (|u₂ σ x| + |B0579.pd 0 (u₂ σ) x| + |B0579.pd 1 (u₂ σ) x| + |lapP (u₂ σ) x|)) hw
    linarith [hC₁ σ hσ x, hC₂ σ hσ x]
  pde σ hσ x := by
    have s1 := (hu₁.slice σ hσ).smooth
    have s2 := (hu₂.slice σ hσ).smooth
    refine ((hu₁.pde σ hσ x).sub (hu₂.pde σ hσ x)).congr_deriv ?_
    rw [pd_sub_eq' s1 s2 0 x, pd_sub_eq' s1 s2 1 x, lapP_sub_eq' s1 s2 x]
    ring

/-- Restriction of a regular cylinder flow to a subinterval. -/
theorem regFlow_mono {c ν s s' T T' : ℝ}
    {v : ℝ → B0579.Plane → UnforcedLeray.Train.Vec} {u : ℝ → B0579.Plane → ℝ}
    (hu : IsRegularCylFlow c ν v s T u) (hs : s ≤ s') (hT : T' ≤ T) :
    IsRegularCylFlow c ν v s' T' u where
  jointCont := hu.jointCont.mono (prod_mono (Icc_subset_Icc hs hT) subset_rfl)
  slice σ hσ := hu.slice σ ⟨hs.trans hσ.1, hσ.2.trans hT⟩
  decay N := by
    obtain ⟨C, hC⟩ := hu.decay N
    exact ⟨C, fun σ hσ x => hC σ ⟨hs.trans hσ.1, hσ.2.trans hT⟩ x⟩
  pde σ hσ x :=
    (hu.pde σ ⟨hs.trans hσ.1, hσ.2.trans hT⟩ x).mono (Icc_subset_Icc hs hT)

/-- Gronwall bound for the `X_{m,c}` energy of regular cylinder flows of a BUC train on `[0, T]`,
uniform in the start age. -/
theorem reg_energy {m ν c T : ℝ} (hm : 0 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 < K ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ u : ℝ → B0579.Plane → ℝ,
      IsRegularCylFlow c ν tr.v s t u →
        cylEnergy c m (u t) ≤ Real.exp (2 * K * (t - s)) * cylEnergy c m (u s) := by
  obtain ⟨Cd, hCd⟩ := cylDiffusionBound m hm
  obtain ⟨V, hV0, hV⟩ := driftC2Bdd_of_buc (tr := tr) hbu hT
  set K : ℝ := (|Cd| + 1) * ν + m * V with hK_def
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, fun s t hs hst htT u hu => ?_⟩
  have hM : ∀ σ ∈ Icc s t, ∀ x : B0579.Plane, |tr.v σ x 0| + |tr.v σ x 1| ≤ 2 * V := by
    intro σ hσ x
    have hσ0 : σ ∈ Icc 0 T := ⟨le_trans hs hσ.1, hσ.2.trans htT⟩
    linarith [(hV σ hσ0 x 0).1, (hV σ hσ0 x 1).1]
  obtain ⟨hcont, hderiv⟩ := regularEnergyDeriv c ν m s t tr.v u hc hu ⟨2 * V, hM⟩
  have hdiss : ∀ τ ∈ Ico s t,
      2 * ∫ x in B0579.cell c, u τ x * (ν * lapP (u τ) x -
          (tr.v τ x 0 * B0579.pd 0 (u τ) x + tr.v τ x 1 * B0579.pd 1 (u τ) x)) *
            (B0579.density m x : ℝ)
        ≤ 2 * K * cylEnergy c m (u τ) := by
    intro τ hτ
    have hτI : τ ∈ Icc s t := ⟨hτ.1, hτ.2.le⟩
    have hsd := hu.slice τ hτI
    obtain ⟨hE, hI1, hD⟩ := hCd c hc (u τ) hsd
    obtain ⟨hT1, hT2, hT'⟩ := cylTransportIBP ν c tr τ (le_trans hs hτ.1) hc
      ⟨2 * V, hM τ hτI⟩ m (u τ) hsd
    have key := t22_dissipation (c := c) (m := m) (Cd := Cd) (U := 2 * V)
      hν hm.le (tr.v τ) (fun _ => (0, 0)) (fun _ => by simp)
      (fun x _ => by simpa using hM τ hτI x) (u τ) hE hI1 hD hT1 hT2 hT'
    have hEnn := t22_energy_nonneg c m (u τ)
    have hK_le : Cd * ν + m * (2 * V) ≤ 2 * K := by
      dsimp [K]
      nlinarith [le_abs_self Cd, abs_nonneg Cd, hν]
    exact key.trans (mul_le_mul_of_nonneg_right hK_le hEnn)
  have hrate : CylEnergyRate c m K (Ico s t) u :=
    ⟨fun τ => 2 * ∫ x in B0579.cell c, u τ x * (ν * lapP (u τ) x -
        (tr.v τ x 0 * B0579.pd 0 (u τ) x + tr.v τ x 1 * B0579.pd 1 (u τ) x)) *
          (B0579.density m x : ℝ),
      fun τ hτ => ⟨hderiv τ hτ, hdiss τ hτ⟩⟩
  exact cyl_gronwall_of_rate hcont hrate hst

/-- `eLpNorm = √(energy)` for `X_{m,c}` functions. -/
theorem eLpNorm_eq_sqrt_energy {c m : ℝ} {g : B0579.Plane → ℝ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    eLpNorm g 2 (B0579.cellMeasure c m) = ENNReal.ofReal (Real.sqrt (cylEnergy c m g)) := by
  rw [← t22_energy_eq_sq_eLpNorm hg, Real.sqrt_sq ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hg.eLpNorm_lt_top.ne]

/-- A weak flow from a cylinder test agrees on the cell with the regular flow from the same data. -/
theorem exists_regular_of_test {m ν c : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) {s : ℝ}
    (hs : 0 ≤ s) {g : B0579.Plane → ℝ} (hg : B0579.IsCylTest c g) :
    ∃ R : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s g R ∧ R s = g ∧
      (∀ T, s ≤ T → IsRegularCylFlow c ν tr.v s T R) ∧
      ∀ w : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s g w → ∀ t, s ≤ t →
        w t =ᵐ[B0579.cellMeasure c m] R t := by
  obtain ⟨R, hR, hRs, hRreg⟩ := freeCylSmoothExists_proof m ν c hm hν hc tr hbu s hs g hg
  refine ⟨R, hR, hRs, hRreg, fun w hw t hst => ?_⟩
  have huniq := (free_cyl_exists_unique m ν c hm hν hc tr hbu s hs g (hg.memLp m)).2 w R hw hR t hst
  exact (B0579.cellMeasure_ac c m).ae_le huniq

/-- Energy bound for weak flows from cylinder tests (via the regular flow). -/
theorem weak_energy {m ν c T : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 < K ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ g : B0579.Plane → ℝ,
      B0579.IsCylTest c g → ∀ w : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s g w →
        cylEnergy c m (w t) ≤ Real.exp (2 * K * (t - s)) * cylEnergy c m g := by
  obtain ⟨K, hK, hE⟩ := reg_energy (m := m) (by linarith) hν hc hbu hT
  refine ⟨K, hK, fun s t hs hst htT g hg w hw => ?_⟩
  obtain ⟨R, hR, hRs, hRreg, hRu⟩ := exists_regular_of_test hm hν hc hbu hs hg
  have h1 : cylEnergy c m (w t) = cylEnergy c m (R t) :=
    t22_energy_congr ((B0579.ac_cellMeasure c m).ae_le (hRu w hw t hst))
  rw [h1]
  have h2 := hE s t hs hst htT R (hRreg t hst)
  rwa [hRs] at h2

/-- Difference bound: two weak flows from cylinder tests, started at `s ≤ s'`, differ at `t ≥ s'` by
at most `exp(K T)` times the gap of the data at `s'`. -/
theorem diff_bound {m ν c T : ℝ} (hm : 8 < m) (hν : 0 < ν) (hc : 0 < c)
    {tr : B0140.TrainSol ν c} (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr) (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s s' t : ℝ, 0 ≤ s → s ≤ s' → s' ≤ t → t ≤ T →
      ∀ g g' : B0579.Plane → ℝ, B0579.IsCylTest c g → B0579.IsCylTest c g' →
      ∀ w w' : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m tr s g w → IsFreeCylFlow m tr s' g' w' →
        eLpNorm (w' t - w t) 2 (B0579.cellMeasure c m) ≤
          ENNReal.ofReal C * eLpNorm (g' - w s') 2 (B0579.cellMeasure c m) := by
  obtain ⟨K, hK, hE⟩ := reg_energy (m := m) (by linarith) hν hc hbu hT
  refine ⟨Real.exp (K * T), Real.one_le_exp (by positivity), ?_⟩
  intro s s' t hs hss' hs't htT g g' hg hg' w w' hw hw'
  have hs' : 0 ≤ s' := hs.trans hss'
  obtain ⟨R, hR, hRs, hRreg, hRu⟩ := exists_regular_of_test hm hν hc hbu hs hg
  obtain ⟨R', hR', hR's, hR'reg, hR'u⟩ := exists_regular_of_test hm hν hc hbu hs' hg'
  have hreg : IsRegularCylFlow c ν tr.v s' t (fun r x => R' r x - R r x) :=
    isRegularCylFlow_sub' (hR'reg t hs't) (regFlow_mono (hRreg t (hss'.trans hs't)) hss' le_rfl)
  have hEn := hE s' t hs' hs't htT _ hreg
  have hmemD : ∀ r, s' ≤ r → MemLp (fun x => R' r x - R r x) 2 (B0579.cellMeasure c m) :=
    fun r hr => (hR'.memX r hr).sub (hR.memX r (hss'.trans hr))
  have hD_t : eLpNorm (w' t - w t) 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => R' t x - R t x) 2 (B0579.cellMeasure c m) := by
    apply eLpNorm_congr_ae
    filter_upwards [hR'u w' hw' t hs't, hRu w hw t (hss'.trans hs't)] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have hD_s : eLpNorm (fun x => R' s' x - R s' x) 2 (B0579.cellMeasure c m) =
      eLpNorm (g' - w s') 2 (B0579.cellMeasure c m) := by
    apply eLpNorm_congr_ae
    filter_upwards [hRu w hw s' hss'] with x h2
    simp only [Pi.sub_apply, h2, hR's]
  rw [hD_t, eLpNorm_eq_sqrt_energy (hmemD t hs't), ← hD_s,
    eLpNorm_eq_sqrt_energy (hmemD s' le_rfl), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hE0 := t22_energy_nonneg c m (fun x => R' s' x - R s' x)
  calc Real.sqrt (cylEnergy c m (fun x => R' t x - R t x))
      ≤ Real.sqrt (Real.exp (2 * K * (t - s')) * cylEnergy c m (fun x => R' s' x - R s' x)) :=
        Real.sqrt_le_sqrt hEn
    _ = Real.exp (K * (t - s')) * Real.sqrt (cylEnergy c m (fun x => R' s' x - R s' x)) := by
        rw [Real.sqrt_mul (Real.exp_pos _).le]
        congr 1
        have he : Real.exp (2 * K * (t - s')) =
            Real.exp (K * (t - s')) * Real.exp (K * (t - s')) := by
          rw [← Real.exp_add]; ring_nf
        rw [he, Real.sqrt_mul_self (Real.exp_pos _).le]
    _ ≤ Real.exp (K * T) * Real.sqrt (cylEnergy c m (fun x => R' s' x - R s' x)) := by
        gcongr
        nlinarith

end UnforcedLeray.Short.IIIa.RelB4locAux
