import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- (E1) **Limit of `C^m` functions with uniformly Cauchy derivatives** (completion argument of
source 1684-1689): if `u_n : Plane → Vec2` are `C^m` and each `D^j u_n`, `j ≤ m`, is uniformly
Cauchy, then the pointwise limit `z` exists and is `C^m` (induction on `m` with
`hasFDerivAt_of_tendstoUniformly`; Mathlib has no ready lemma). -/
def LimitContDiff : Prop :=
  ∀ (m : ℕ) (u : ℕ → Plane → Vec2), (∀ n, ContDiff ℝ m (u n)) →
    (∀ j : ℕ, j ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
      ‖iteratedFDeriv ℝ j (u n) x - iteratedFDeriv ℝ j (u p) x‖ < ε) →
    ∃ z : Plane → Vec2, ContDiff ℝ m z ∧ ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (z x))

/-- (E2) **Smooth approximants in `H^k`** (`Sob.W.exists_seq_cylSmooth`, `Lib/SobolevC/CylDensity.lean:760`,
upgraded to `W.ofCylSmooth` elements via `W.value_injective` as in `TrainB.exists_smoothH2_sequence`,
`WeakEmbedding.lean:531`): every `y ∈ H^k(cell; ℝ²)` is a limit of `W.ofCylSmooth u_n`. -/
def SmoothSeqH : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (k : ℕ) (y : UnforcedLeray.Cyl.H ℝ Vec2 c 0 k),
    ∃ (u : ℕ → Plane → Vec2) (hu : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (u n)),
      Tendsto (fun n => UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)) atTop (𝓝 y)

/-- (E3) **Additivity of `W.ofCylSmooth`** for `Vec2`, general `k` (cf. `TrainB.ofCylSmooth_sub_eq`,
`WeakEmbedding.lean:491`, scalar `k = 2`). -/
def OfCylSmoothSub : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (k : ℕ) (f g : Plane → Vec2)
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (hfg : UnforcedLeray.Sob.IsCylSmooth c (fun x => f x - g x)),
    UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (fun x => f x - g x) hfg =
      UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf -
      UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg

/-- (E4) **A.e. identification of the pointwise limit**: if smooth `u_n → z` pointwise and
`W.ofCylSmooth u_n → y` in `H^k`, then `z = value y` a.e. on the cell (`tendstoInMeasure_of_tendsto_Lp`
+ `exists_seq_tendsto_ae` exactly as `TrainB.exists_scalarH2_bcf_representative`,
`WeakEmbedding.lean:599`, with `scalarH2_measure_eq_cell`, `WeakEmbedding.lean:27`). -/
def AeLimitH : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (k : ℕ) (y : UnforcedLeray.Cyl.H ℝ Vec2 c 0 k)
    (u : ℕ → Plane → Vec2) (hu : ∀ n, UnforcedLeray.Sob.IsCylSmooth c (u n)) (z : Plane → Vec2),
    (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (z x))) →
    Tendsto (fun n => UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n)) atTop (𝓝 y) →
    z =ᵐ[UnforcedLeray.Cyl.cellμ c]
      ((UnforcedLeray.Sob.W.value _ _ _ _ _ _ y : Plane → Vec2))

theorem extendFromSmooth_of (h1 : LimitContDiff) (h2 : SmoothSeqH) (h3 : OfCylSmoothSub)
    (h4 : AeLimitH) : ExtendFromSmooth := by
  intro c hc m k C hC hb y
  obtain ⟨u, hu, hlim⟩ := h2 c hc k y
  set a := fun n => UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := k) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (u n) (hu n) with ha
  have hcau := hlim.cauchySeq
  have hcd : ∀ n, ContDiff ℝ m (u n) := fun n => (hu n).smooth.of_le (by exact_mod_cast le_top)
  have hunif : ∀ j : ℕ, j ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p, N ≤ n → N ≤ p → ∀ x : Plane,
      ‖iteratedFDeriv ℝ j (u n) x - iteratedFDeriv ℝ j (u p) x‖ < ε := by
    intro j hj ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hcau (ε / (C + 1)) (by positivity)
    refine ⟨N, fun n p hn hp x => ?_⟩
    have hdist := hN n hn p hp
    rw [dist_eq_norm] at hdist
    have hj' : ∀ q, ContDiff ℝ j (u q) := fun q => (hu q).smooth.of_le (by exact_mod_cast le_top)
    have hsub : iteratedFDeriv ℝ j (u n) x - iteratedFDeriv ℝ j (u p) x =
        iteratedFDeriv ℝ j (fun y => u n y - u p y) x :=
      (iteratedFDeriv_sub_apply (hj' n).contDiffAt (hj' p).contDiffAt).symm
    have hfg := UnforcedLeray.HeatCylinder.isCylSmooth_sub (hu n) (hu p)
    have := hb (fun y => u n y - u p y) hfg j hj x
    rw [h3 c hc k (u n) (u p) (hu n) (hu p) hfg] at this
    rw [hsub]
    have h5 : C * ‖a n - a p‖ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hdist.le hC
    have h6 : C * (ε / (C + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt (le_trans this h5) h6
  obtain ⟨z, hz, hzl⟩ := h1 m u hcd hunif
  refine ⟨z, hz, ?_, ?_, h4 c hc k y u hu z hzl hlim⟩
  · intro x
    have h1' : Tendsto (fun n => u n (x.1 + c, x.2)) atTop (𝓝 (z (x.1 + c, x.2))) := hzl _
    have h2' : Tendsto (fun n => u n (x.1 + c, x.2)) atTop (𝓝 (z x)) := by
      refine (hzl x).congr (fun n => ?_)
      have e : (x.1 + c, x.2) = x + (c, 0) := by ext <;> simp
      rw [e]
      exact ((hu n).periodic x).symm
    exact tendsto_nhds_unique h1' h2'
  · intro x
    have hn : Tendsto (fun n => ‖u n x‖) atTop (𝓝 ‖z x‖) := (hzl x).norm
    have hy : Tendsto (fun n => C * ‖a n‖) atTop (𝓝 (C * ‖y‖)) := (hlim.norm).const_mul C
    refine le_of_tendsto_of_tendsto' hn hy (fun n => ?_)
    have := hb (u n) (hu n) 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
