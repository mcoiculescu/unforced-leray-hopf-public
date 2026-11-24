import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2.BlockB1.HeatLiftHelp

/-!
# Weighted Fréchet-jet calculus and one-sided Landau interpolation on `ProfilePoint`

Source of record: `the November 2 reference manuscript`, lines 427-459, 516-526,
1243-1285.

Defines `WtdProfJet m w α f` on `ProfilePoint = ℝ × (ℝ × ℝ)` (`x = (q, (η, s))`, `1 ≤ s = x.2.2`),
establishes closure under linear combinations, products, directional partials (`partialQ`,
`partialEta`, `partialAge`), coordinate multipliers (`η`, `s`), `ageOperator`, `ageShift`, heat
profiles `lhP ν k` / `heatSumFam M`, and one-sided half-ball Landau interpolation
`wtdProfJet_of_zero_and_unweighted`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0188 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.FarDecaySub
open UnforcedLeray.Short.PartIIIb.Concrete.LateHeatDecomp2Sub

namespace UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux

/-! ### 1. Definition and algebraic/calculus closure of `WtdProfJet` -/

/-- A scalar profile `f : ProfilePoint → ℝ` is `C^∞` on `ageDomain = {x | 0 < x.2.2}` and has
`(1 + |η|)^w`-weighted Fréchet derivatives of orders `≤ m` bounded by `C * s^α` on `1 ≤ s`. -/
def WtdProfJet (m w : ℕ) (α : ℝ) (f : ProfilePoint → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f ageDomain ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ l ≤ m,
      (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f x‖ ≤ C * x.2.2 ^ α

theorem WtdProfJet.congr {m w : ℕ} {α : ℝ} {f g : ProfilePoint → ℝ}
    (hf : WtdProfJet m w α f) (hfg : EqOn f g ageDomain) :
    WtdProfJet m w α g := by
  obtain ⟨hsm, C, hC0, hbd⟩ := hf
  refine ⟨hsm.congr hfg.symm, C, hC0, fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hev : g =ᶠ[𝓝 x] f :=
    Filter.eventuallyEq_of_mem (B0185.isOpen_ageDomain.mem_nhds hx0) (fun y hy => (hfg hy).symm)
  rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds]
  exact hbd x hx1 l hl

theorem WtdProfJet.mono_m {m m' w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hm : m' ≤ m) (hf : WtdProfJet m w α f) :
    WtdProfJet m' w α f :=
  ⟨hf.1, let ⟨C, hC0, hbd⟩ := hf.2; ⟨C, hC0, fun x hx1 l hl => hbd x hx1 l (hl.trans hm)⟩⟩

theorem WtdProfJet.mono_w {m w w' : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hw : w' ≤ w) (hf : WtdProfJet m w α f) :
    WtdProfJet m w' α f := by
  obtain ⟨hsm, C, hC0, hbd⟩ := hf
  refine ⟨hsm, C, hC0, fun x hx1 l hl => ?_⟩
  have h1 : 1 ≤ 1 + |x.2.1| := by linarith [abs_nonneg x.2.1]
  have hpow : (1 + |x.2.1|) ^ w' ≤ (1 + |x.2.1|) ^ w := pow_le_pow_right₀ h1 hw
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hbd x hx1 l hl)

theorem WtdProfJet.mono_alpha {m w : ℕ} {α α' : ℝ} {f : ProfilePoint → ℝ}
    (hα : α ≤ α') (hf : WtdProfJet m w α f) :
    WtdProfJet m w α' f := by
  obtain ⟨hsm, C, hC0, hbd⟩ := hf
  refine ⟨hsm, C, hC0, fun x hx1 l hl => ?_⟩
  exact (hbd x hx1 l hl).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hα) hC0)

theorem WtdProfJet.zero (m w : ℕ) (α : ℝ) : WtdProfJet m w α (fun _ => 0) := by
  refine ⟨contDiffOn_const, 0, le_rfl, fun x _ l _ => ?_⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · rw [iteratedFDeriv_const_of_ne hl.ne' (0 : ℝ)]; simp

theorem WtdProfJet.add {m w : ℕ} {α : ℝ} {f g : ProfilePoint → ℝ}
    (hf : WtdProfJet m w α f) (hg : WtdProfJet m w α g) :
    WtdProfJet m w α (fun x => f x + g x) := by
  obtain ⟨cf, Cf, hCf0, hbf⟩ := hf
  obtain ⟨cg, Cg, hCg0, hbg⟩ := hg
  refine ⟨cf.add cg, Cf + Cg, add_nonneg hCf0 hCg0, fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hnhds : ageDomain ∈ 𝓝 x := B0185.isOpen_ageDomain.mem_nhds hx0
  have hadd : iteratedFDeriv ℝ l (fun y => f y + g y) x =
      iteratedFDeriv ℝ l f x + iteratedFDeriv ℝ l g x :=
    iteratedFDeriv_add_apply ((cf.contDiffAt hnhds).of_le (by exact_mod_cast le_top))
      ((cg.contDiffAt hnhds).of_le (by exact_mod_cast le_top))
  have hw0 : 0 ≤ (1 + |x.2.1|) ^ w := by positivity
  have hnorm : ‖iteratedFDeriv ℝ l (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
    rw [hadd]; exact norm_add_le _ _
  calc (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l (fun y => f y + g y) x‖
      ≤ (1 + |x.2.1|) ^ w * (‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖) :=
        mul_le_mul_of_nonneg_left hnorm hw0
    _ = (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f x‖ +
          (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l g x‖ := by ring
    _ ≤ Cf * x.2.2 ^ α + Cg * x.2.2 ^ α := add_le_add (hbf x hx1 l hl) (hbg x hx1 l hl)
    _ = (Cf + Cg) * x.2.2 ^ α := by ring

theorem WtdProfJet.const_mul {m w : ℕ} {α : ℝ} (c : ℝ) {f : ProfilePoint → ℝ}
    (hf : WtdProfJet m w α f) :
    WtdProfJet m w α (fun x => c * f x) := by
  obtain ⟨cf, C, hC0, hbf⟩ := hf
  set L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ c
  refine ⟨contDiffOn_const.mul cf, ‖L‖ * C, mul_nonneg (norm_nonneg _) hC0, fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hnhds : ageDomain ∈ 𝓝 x := B0185.isOpen_ageDomain.mem_nhds hx0
  have heq : (fun y : ProfilePoint => c * f y) = L ∘ f := rfl
  have hL : ‖iteratedFDeriv ℝ l (fun y => c * f y) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ l f x‖ := by
    rw [heq]
    exact L.norm_iteratedFDeriv_comp_left (cf.contDiffAt hnhds) (by exact_mod_cast le_top)
  have hw0 : 0 ≤ (1 + |x.2.1|) ^ w := by positivity
  calc (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l (fun y => c * f y) x‖
      ≤ (1 + |x.2.1|) ^ w * (‖L‖ * ‖iteratedFDeriv ℝ l f x‖) :=
        mul_le_mul_of_nonneg_left hL hw0
    _ = ‖L‖ * ((1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f x‖) := by ring
    _ ≤ ‖L‖ * (C * x.2.2 ^ α) := mul_le_mul_of_nonneg_left (hbf x hx1 l hl) (norm_nonneg _)
    _ = (‖L‖ * C) * x.2.2 ^ α := by ring

theorem WtdProfJet.neg {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet m w α f) :
    WtdProfJet m w α (fun x => -f x) := by
  have h := hf.const_mul (-1)
  have heq : (fun x : ProfilePoint => (-1 : ℝ) * f x) = fun x => -f x := by
    funext x; ring
  rwa [heq] at h

theorem WtdProfJet.sub {m w : ℕ} {α : ℝ} {f g : ProfilePoint → ℝ}
    (hf : WtdProfJet m w α f) (hg : WtdProfJet m w α g) :
    WtdProfJet m w α (fun x => f x - g x) := by
  have h := hf.add hg.neg
  have heq : (fun x : ProfilePoint => f x + -g x) = fun x => f x - g x :=
    funext fun x => (sub_eq_add_neg (f x) (g x)).symm
  rwa [heq] at h

theorem WtdProfJet.sum {m w : ℕ} {α : ℝ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {F : ι → ProfilePoint → ℝ} (h : ∀ i ∈ s, WtdProfJet m w α (F i)) :
    WtdProfJet m w α (fun x => ∑ i ∈ s, F i x) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using WtdProfJet.zero m w α
  | @insert a s ha ih =>
    have heq : (fun x : ProfilePoint => ∑ i ∈ insert a s, F i x) =
        fun x => F a x + ∑ i ∈ s, F i x :=
      funext fun x => Finset.sum_insert ha
    rw [heq]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiffOn_fderiv_ageDomain {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (fderiv ℝ f) ageDomain := by
  have hw : ContDiffOn ℝ ∞ (fderivWithin ℝ f ageDomain) ageDomain :=
    hf.fderivWithin B0185.isOpen_ageDomain.uniqueDiffOn (m := ∞) (by simp)
  exact hw.congr fun y hy => (fderivWithin_of_isOpen B0185.isOpen_ageDomain hy).symm

/-- Directional derivative along any constant vector `v : ProfilePoint` shifts the order budget by
`1` with no loss in weight `w` or age exponent `α`. -/
theorem WtdProfJet.dirDeriv {m w : ℕ} {α : ℝ} (v : ProfilePoint) {f : ProfilePoint → ℝ}
    (hf : WtdProfJet (m + 1) w α f) :
    WtdProfJet m w α (fun x => fderiv ℝ f x v) := by
  obtain ⟨cf, C, hC0, hbf⟩ := hf
  set L : (ProfilePoint →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have cfd : ContDiffOn ℝ ∞ (fderiv ℝ f) ageDomain := contDiffOn_fderiv_ageDomain cf
  have cdir : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) ageDomain :=
    L.contDiff.comp_contDiffOn cfd
  refine ⟨cdir, ‖L‖ * C, mul_nonneg (norm_nonneg L) hC0, fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hnhds : ageDomain ∈ 𝓝 x := B0185.isOpen_ageDomain.mem_nhds hx0
  have heq : (fun y : ProfilePoint => fderiv ℝ f y v) = L ∘ fderiv ℝ f := rfl
  have hL : ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ f y v) x‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ (l + 1) f x‖ := by
    rw [heq, ← norm_iteratedFDeriv_fderiv]
    exact L.norm_iteratedFDeriv_comp_left (cfd.contDiffAt hnhds) (by exact_mod_cast le_top)
  have hw0 : 0 ≤ (1 + |x.2.1|) ^ w := by positivity
  calc (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ f y v) x‖
      ≤ (1 + |x.2.1|) ^ w * (‖L‖ * ‖iteratedFDeriv ℝ (l + 1) f x‖) :=
        mul_le_mul_of_nonneg_left hL hw0
    _ = ‖L‖ * ((1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ (l + 1) f x‖) := by ring
    _ ≤ ‖L‖ * (C * x.2.2 ^ α) :=
        mul_le_mul_of_nonneg_left (hbf x hx1 (l + 1) (Nat.succ_le_succ hl)) (norm_nonneg L)
    _ = (‖L‖ * C) * x.2.2 ^ α := by ring

theorem WtdProfJet.partialQ {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet (m + 1) w α f) :
    WtdProfJet m w α (UnforcedLeray.B0184.partialQ f) :=
  hf.dirDeriv eqDir

theorem WtdProfJet.partialEta {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet (m + 1) w α f) :
    WtdProfJet m w α (UnforcedLeray.B0184.partialEta f) :=
  hf.dirDeriv eηDir

theorem WtdProfJet.partialAge {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet (m + 1) w α f) :
    WtdProfJet m w α (UnforcedLeray.B0184.partialAge f) :=
  hf.dirDeriv esDir

/-- Pointwise product of two `WtdProfJet` profiles adds weights and age exponents. -/
theorem WtdProfJet.mul {m w₁ w₂ : ℕ} {α₁ α₂ : ℝ} {f g : ProfilePoint → ℝ}
    (hf : WtdProfJet m w₁ α₁ f) (hg : WtdProfJet m w₂ α₂ g) :
    WtdProfJet m (w₁ + w₂) (α₁ + α₂) (fun x => f x * g x) := by
  obtain ⟨cf, Cf, hCf0, hbf⟩ := hf
  obtain ⟨cg, Cg, hCg0, hbg⟩ := hg
  set B_comb : ℝ := ∑ l ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)
  have hBc0 : 0 ≤ B_comb :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨cf.mul cg, B_comb * Cf * Cg, mul_nonneg (mul_nonneg hBc0 hCf0) hCg0,
    fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hleib : ‖iteratedFDeriv ℝ l (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (l - i) g x‖ := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun y => f y * g y) l B0185.isOpen_ageDomain hx0]
    refine (norm_iteratedFDerivWithin_mul_le cf cg B0185.isOpen_ageDomain.uniqueDiffOn hx0
      (n := l) (by exact_mod_cast le_top)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDerivWithin_of_isOpen i B0185.isOpen_ageDomain hx0,
      iteratedFDerivWithin_of_isOpen (l - i) B0185.isOpen_ageDomain hx0]
  have hw0 : 0 ≤ (1 + |x.2.1|) ^ (w₁ + w₂) := by positivity
  have hl_sub : ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) ≤ B_comb :=
    Finset.single_le_sum (f := fun k => ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  calc (1 + |x.2.1|) ^ (w₁ + w₂) * ‖iteratedFDeriv ℝ l (fun y => f y * g y) x‖
      ≤ (1 + |x.2.1|) ^ (w₁ + w₂) * ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (l - i) g x‖ :=
        mul_le_mul_of_nonneg_left hleib hw0
    _ = ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
          (((1 + |x.2.1|) ^ w₁ * ‖iteratedFDeriv ℝ i f x‖) *
            ((1 + |x.2.1|) ^ w₂ * ‖iteratedFDeriv ℝ (l - i) g x‖)) := by
        rw [pow_add, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
          ((Cf * x.2.2 ^ α₁) * (Cg * x.2.2 ^ α₂)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : i ≤ m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hl
        have hli_le : l - i ≤ m := (Nat.sub_le l i).trans hl
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hbf x hx1 i hi_le) (hbg x hx1 (l - i) hli_le)
            (by positivity) (mul_nonneg hCf0 (Real.rpow_nonneg hx0.le _)))
          (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (Cf * Cg * x.2.2 ^ (α₁ + α₂)) := by
        rw [← Finset.sum_mul, Real.rpow_add hx0]
        ring
    _ ≤ B_comb * Cf * Cg * x.2.2 ^ (α₁ + α₂) := by
        have hpos : 0 ≤ Cf * Cg * x.2.2 ^ (α₁ + α₂) :=
          mul_nonneg (mul_nonneg hCf0 hCg0) (Real.rpow_nonneg hx0.le _)
        calc (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (Cf * Cg * x.2.2 ^ (α₁ + α₂))
            ≤ B_comb * (Cf * Cg * x.2.2 ^ (α₁ + α₂)) := mul_le_mul_of_nonneg_right hl_sub hpos
          _ = B_comb * Cf * Cg * x.2.2 ^ (α₁ + α₂) := by ring

/-- Norm of `iteratedFDeriv` of a continuous linear map `L : ProfilePoint →L[ℝ] ℝ`. -/
theorem norm_iteratedFDeriv_clm_le (L : ProfilePoint →L[ℝ] ℝ) (x : ProfilePoint) :
    ∀ i : ℕ, ‖iteratedFDeriv ℝ i L x‖ ≤ if i = 0 then |L x| else if i = 1 then ‖L‖ else 0
  | 0 => by simp [norm_iteratedFDeriv_zero]
  | 1 => by simp [norm_iteratedFDeriv_one, L.fderiv]
  | j + 2 => by
    rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (fun y => L y) = fun _ : ProfilePoint => L :=
      funext fun _ => L.fderiv
    rw [hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) L]
    simp

/-- Coordinate multiplier `x ↦ x.2.2` (`s`) belongs to `WtdProfJet m 0 1`. -/
theorem coordAge_wtdProfJet (m : ℕ) :
    WtdProfJet m 0 1 (fun x : ProfilePoint => x.2.2) := by
  set πAge : ProfilePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  refine ⟨πAge.contDiff.contDiffOn, max 1 ‖πAge‖, by positivity, fun x hx1 l _ => ?_⟩
  rw [pow_zero, one_mul, Real.rpow_one]
  have hclm := norm_iteratedFDeriv_clm_le πAge x l
  have hx_eq : πAge x = x.2.2 := rfl
  rcases l with _ | _ | j
  · simp only [↓reduceIte, hx_eq, abs_of_nonneg (zero_le_one.trans hx1)] at hclm
    calc ‖iteratedFDeriv ℝ 0 (fun x : ProfilePoint => x.2.2) x‖
        ≤ x.2.2 := hclm
      _ = 1 * x.2.2 := (one_mul _).symm
      _ ≤ max 1 ‖πAge‖ * x.2.2 :=
          mul_le_mul_of_nonneg_right (le_max_left 1 ‖πAge‖) (zero_le_one.trans hx1)
  · simp only [Nat.succ_ne_zero, ↓reduceIte] at hclm
    calc ‖iteratedFDeriv ℝ 1 (fun x : ProfilePoint => x.2.2) x‖
        ≤ ‖πAge‖ := hclm
      _ ≤ max 1 ‖πAge‖ * 1 := by rw [mul_one]; exact le_max_right 1 ‖πAge‖
      _ ≤ max 1 ‖πAge‖ * x.2.2 := mul_le_mul_of_nonneg_left hx1 (by positivity)
  · have hj0 : j + 2 ≠ 0 := by omega
    have hj1 : j + 2 ≠ 1 := by omega
    simp only [hj0, hj1, ↓reduceIte] at hclm
    exact hclm.trans (mul_nonneg (by positivity) (zero_le_one.trans hx1))

theorem WtdProfJet.mul_age {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet m w α f) :
    WtdProfJet m w (α + 1) (fun x => x.2.2 * f x) := by
  have h := (coordAge_wtdProfJet m).mul hf
  rw [zero_add, add_comm (1 : ℝ) α] at h
  exact h

/-- Multiplying by `x.2.1` (`η`) consumes one power of `(1 + |η|)` with no loss in `α`. -/
theorem WtdProfJet.mul_eta {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet m (w + 1) α f) :
    WtdProfJet m w α (fun x => x.2.1 * f x) := by
  obtain ⟨cf, C, hC0, hbf⟩ := hf
  set πEta : ProfilePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  set K_π : ℝ := max 1 ‖πEta‖
  have hKπ : 0 ≤ K_π := by unfold K_π; positivity
  set B_comb : ℝ := ∑ l ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)
  have hBc0 : 0 ≤ B_comb :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨πEta.contDiff.contDiffOn.mul cf, B_comb * K_π * C,
    mul_nonneg (mul_nonneg hBc0 hKπ) hC0, fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hπ_jet : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun y : ProfilePoint => y.2.1) x‖ ≤
      K_π * (1 + |x.2.1|) := by
    intro i
    have hclm := norm_iteratedFDeriv_clm_le πEta x i
    have hx_eq : πEta x = x.2.1 := rfl
    have h1 : 1 ≤ 1 + |x.2.1| := by linarith [abs_nonneg x.2.1]
    rcases i with _ | _ | j
    · simp only [↓reduceIte, hx_eq] at hclm
      calc ‖iteratedFDeriv ℝ 0 (fun y : ProfilePoint => y.2.1) x‖
          ≤ |x.2.1| := hclm
        _ ≤ 1 * (1 + |x.2.1|) := by linarith
        _ ≤ K_π * (1 + |x.2.1|) := mul_le_mul_of_nonneg_right (le_max_left 1 ‖πEta‖) (by linarith)
    · simp only [Nat.succ_ne_zero, ↓reduceIte] at hclm
      calc ‖iteratedFDeriv ℝ 1 (fun y : ProfilePoint => y.2.1) x‖
          ≤ ‖πEta‖ * 1 := by rw [mul_one]; exact hclm
        _ ≤ K_π * (1 + |x.2.1|) := mul_le_mul (le_max_right 1 ‖πEta‖) h1 zero_le_one hKπ
    · have hj0 : j + 2 ≠ 0 := by omega
      have hj1 : j + 2 ≠ 1 := by omega
      simp only [hj0, hj1, ↓reduceIte] at hclm
      exact hclm.trans (mul_nonneg hKπ (by linarith))
  have hleib : ‖iteratedFDeriv ℝ l (fun y : ProfilePoint => y.2.1 * f y) x‖ ≤
      ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : ProfilePoint => y.2.1) x‖ *
        ‖iteratedFDeriv ℝ (l - i) f x‖ := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
      (f := fun y : ProfilePoint => y.2.1 * f y) l B0185.isOpen_ageDomain hx0]
    refine (norm_iteratedFDerivWithin_mul_le πEta.contDiff.contDiffOn cf
      B0185.isOpen_ageDomain.uniqueDiffOn hx0 (n := l) (by exact_mod_cast le_top)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDerivWithin_of_isOpen i B0185.isOpen_ageDomain hx0,
      iteratedFDerivWithin_of_isOpen (l - i) B0185.isOpen_ageDomain hx0]
    rfl
  have hw0 : 0 ≤ (1 + |x.2.1|) ^ w := by positivity
  have hl_sub : ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) ≤ B_comb :=
    Finset.single_le_sum (f := fun k => ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  calc (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l (fun y : ProfilePoint => y.2.1 * f y) x‖
      ≤ (1 + |x.2.1|) ^ w * ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : ProfilePoint => y.2.1) x‖ *
          ‖iteratedFDeriv ℝ (l - i) f x‖ :=
        mul_le_mul_of_nonneg_left hleib hw0
    _ ≤ ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) *
          (K_π * ((1 + |x.2.1|) ^ (w + 1) * ‖iteratedFDeriv ℝ (l - i) f x‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := mul_le_mul_of_nonneg_right (hπ_jet i) (norm_nonneg (iteratedFDeriv ℝ (l - i) f x))
        have h2 := mul_le_mul_of_nonneg_left h1 ((Nat.cast_nonneg _) : (0 : ℝ) ≤ (Nat.choose l i : ℝ))
        have h3 := mul_le_mul_of_nonneg_left h2 hw0
        calc (1 + |x.2.1|) ^ w * ((Nat.choose l i : ℝ) *
                ‖iteratedFDeriv ℝ i (fun y : ProfilePoint => y.2.1) x‖ *
                ‖iteratedFDeriv ℝ (l - i) f x‖)
            = (1 + |x.2.1|) ^ w * ((Nat.choose l i : ℝ) *
                (‖iteratedFDeriv ℝ i (fun y : ProfilePoint => y.2.1) x‖ *
                  ‖iteratedFDeriv ℝ (l - i) f x‖)) := by ring
          _ ≤ (1 + |x.2.1|) ^ w * ((Nat.choose l i : ℝ) *
                (K_π * (1 + |x.2.1|) * ‖iteratedFDeriv ℝ (l - i) f x‖)) := h3
          _ = (Nat.choose l i : ℝ) *
                (K_π * ((1 + |x.2.1|) ^ (w + 1) * ‖iteratedFDeriv ℝ (l - i) f x‖)) := by
              rw [pow_succ]; ring
    _ ≤ ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) * (K_π * (C * x.2.2 ^ α)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbf x hx1 (l - i) ((Nat.sub_le l i).trans hl)) hKπ)
          (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (K_π * C * x.2.2 ^ α) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ B_comb * K_π * C * x.2.2 ^ α := by
        have hpos : 0 ≤ K_π * C * x.2.2 ^ α :=
          mul_nonneg (mul_nonneg hKπ hC0) (Real.rpow_nonneg hx0.le _)
        calc (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (K_π * C * x.2.2 ^ α)
            ≤ B_comb * (K_π * C * x.2.2 ^ α) := mul_le_mul_of_nonneg_right hl_sub hpos
          _ = B_comb * K_π * C * x.2.2 ^ α := by ring

theorem WtdProfJet.ageOp {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : WtdProfJet (m + 1) (w + 1) α f) :
    WtdProfJet m w (α + 1) (ageOperator f) := by
  have h1 : WtdProfJet m w (α + 1) (fun x => x.2.1 * UnforcedLeray.B0184.partialEta f x) :=
    (hf.partialEta.mul_eta).mono_alpha (by linarith)
  have h2 : WtdProfJet m w (α + 1) (fun x => 2 * (x.2.2 * UnforcedLeray.B0184.partialAge f x)) :=
    (((hf.partialAge.mono_w (Nat.le_succ w)).mul_age).const_mul 2)
  have hsum := h1.add h2
  refine hsum.congr fun x _ => ?_
  unfold ageOperator
  ring

theorem WtdProfJet.ageShift {m w : ℕ} {α : ℝ} (k : ℝ) {f : ProfilePoint → ℝ}
    (hf : WtdProfJet (m + 1) (w + 1) α f) :
    WtdProfJet m w (α + 1) (UnforcedLeray.B0188.ageShift k f) := by
  have h1 := hf.ageOp
  have h2 := ((hf.mono_m (Nat.le_succ m)).mono_w (Nat.le_succ w)).mono_alpha
    (by linarith : α ≤ α + 1)
  have hsum := h1.add (h2.const_mul k)
  refine hsum.congr fun x _ => ?_
  unfold UnforcedLeray.B0188.ageShift
  ring

/-! ### 2. Upgrading `m → m + 1` from `(partialQ, partialEta, partialAge)` and heat profiles `lhP` -/

theorem wtdProfJet_succ_of_partials {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h0 : ∀ x : ProfilePoint, 1 ≤ x.2.2 → (1 + |x.2.1|) ^ w * |f x| ≤ C₀ * x.2.2 ^ α)
    (hQ : WtdProfJet m w α (UnforcedLeray.B0184.partialQ f))
    (hE : WtdProfJet m w α (UnforcedLeray.B0184.partialEta f))
    (hA : WtdProfJet m w α (UnforcedLeray.B0184.partialAge f)) :
    WtdProfJet (m + 1) w α f := by
  obtain ⟨cQ, CQ, hCQ0, hbQ⟩ := hQ
  obtain ⟨cE, CE, hCE0, hbE⟩ := hE
  obtain ⟨cA, CA, hCA0, hbA⟩ := hA
  set πQ : ProfilePoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  set πEta : ProfilePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  set πAge : ProfilePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  set LQ : ℝ →L[ℝ] (ProfilePoint →L[ℝ] ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight πQ
  set LE : ℝ →L[ℝ] (ProfilePoint →L[ℝ] ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight πEta
  set LA : ℝ →L[ℝ] (ProfilePoint →L[ℝ] ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight πAge
  have hfd_eq : fderiv ℝ f = fun y =>
      LQ (UnforcedLeray.B0184.partialQ f y) +
        LE (UnforcedLeray.B0184.partialEta f y) +
        LA (UnforcedLeray.B0184.partialAge f y) := by
    funext y
    refine ContinuousLinearMap.ext fun u => ?_
    have hu : u = u.1 • eqDir + u.2.1 • eηDir + u.2.2 • esDir := by
      ext <;> simp [eqDir, eηDir, esDir]
    conv_lhs => rw [hu]
    rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    change u.1 * partialQ f y + u.2.1 * partialEta f y + u.2.2 * partialAge f y =
      partialQ f y * u.1 + partialEta f y * u.2.1 + partialAge f y * u.2.2
    ring
  refine ⟨hf, C₀ + ‖LQ‖ * CQ + ‖LE‖ * CE + ‖LA‖ * CA, by positivity, fun x hx1 l hl => ?_⟩
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  have hrp0 : 0 ≤ x.2.2 ^ α := Real.rpow_nonneg hx0.le _
  rcases l with _ | l'
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have hb0 := h0 x hx1
    have hle : C₀ ≤ C₀ + ‖LQ‖ * CQ + ‖LE‖ * CE + ‖LA‖ * CA := by
      have : 0 ≤ ‖LQ‖ * CQ + ‖LE‖ * CE + ‖LA‖ * CA := by positivity
      linarith
    exact hb0.trans (mul_le_mul_of_nonneg_right hle hrp0)
  · have hl' : l' ≤ m := Nat.le_of_succ_le_succ hl
    have hnhds : ageDomain ∈ 𝓝 x := B0185.isOpen_ageDomain.mem_nhds hx0
    let gQ : ProfilePoint → (ProfilePoint →L[ℝ] ℝ) := LQ ∘ UnforcedLeray.B0184.partialQ f
    let gE : ProfilePoint → (ProfilePoint →L[ℝ] ℝ) := LE ∘ UnforcedLeray.B0184.partialEta f
    let gA : ProfilePoint → (ProfilePoint →L[ℝ] ℝ) := LA ∘ UnforcedLeray.B0184.partialAge f
    have cgQ : ContDiffAt ℝ ∞ gQ x := LQ.contDiff.contDiffAt.comp x (cQ.contDiffAt hnhds)
    have cgE : ContDiffAt ℝ ∞ gE x := LE.contDiff.contDiffAt.comp x (cE.contDiffAt hnhds)
    have cgA : ContDiffAt ℝ ∞ gA x := LA.contDiff.contDiffAt.comp x (cA.contDiffAt hnhds)
    have hadd1 : iteratedFDeriv ℝ l' (fun y => gQ y + gE y + gA y) x =
        iteratedFDeriv ℝ l' (fun y => gQ y + gE y) x + iteratedFDeriv ℝ l' gA x :=
      iteratedFDeriv_add_apply ((cgQ.add cgE).of_le (by exact_mod_cast le_top))
        (cgA.of_le (by exact_mod_cast le_top))
    have hadd2 : iteratedFDeriv ℝ l' (fun y => gQ y + gE y) x =
        iteratedFDeriv ℝ l' gQ x + iteratedFDeriv ℝ l' gE x :=
      iteratedFDeriv_add_apply (cgQ.of_le (by exact_mod_cast le_top))
        (cgE.of_le (by exact_mod_cast le_top))
    have hQ_le : ‖iteratedFDeriv ℝ l' gQ x‖ ≤
        ‖LQ‖ * ‖iteratedFDeriv ℝ l' (UnforcedLeray.B0184.partialQ f) x‖ :=
      LQ.norm_iteratedFDeriv_comp_left (cQ.contDiffAt hnhds) (by exact_mod_cast le_top)
    have hE_le : ‖iteratedFDeriv ℝ l' gE x‖ ≤
        ‖LE‖ * ‖iteratedFDeriv ℝ l' (UnforcedLeray.B0184.partialEta f) x‖ :=
      LE.norm_iteratedFDeriv_comp_left (cE.contDiffAt hnhds) (by exact_mod_cast le_top)
    have hA_le : ‖iteratedFDeriv ℝ l' gA x‖ ≤
        ‖LA‖ * ‖iteratedFDeriv ℝ l' (UnforcedLeray.B0184.partialAge f) x‖ :=
      LA.norm_iteratedFDeriv_comp_left (cA.contDiffAt hnhds) (by exact_mod_cast le_top)
    have htot : ‖iteratedFDeriv ℝ (l' + 1) f x‖ ≤
        ‖LQ‖ * ‖iteratedFDeriv ℝ l' (UnforcedLeray.B0184.partialQ f) x‖ +
          ‖LE‖ * ‖iteratedFDeriv ℝ l' (UnforcedLeray.B0184.partialEta f) x‖ +
          ‖LA‖ * ‖iteratedFDeriv ℝ l' (UnforcedLeray.B0184.partialAge f) x‖ := by
      rw [← norm_iteratedFDeriv_fderiv, hfd_eq]
      change ‖iteratedFDeriv ℝ l' (fun y => gQ y + gE y + gA y) x‖ ≤ _
      rw [hadd1, hadd2]
      calc ‖iteratedFDeriv ℝ l' gQ x + iteratedFDeriv ℝ l' gE x + iteratedFDeriv ℝ l' gA x‖
          ≤ ‖iteratedFDeriv ℝ l' gQ x + iteratedFDeriv ℝ l' gE x‖ +
              ‖iteratedFDeriv ℝ l' gA x‖ := norm_add_le _ _
        _ ≤ ‖iteratedFDeriv ℝ l' gQ x‖ + ‖iteratedFDeriv ℝ l' gE x‖ +
              ‖iteratedFDeriv ℝ l' gA x‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add hQ_le hE_le) hA_le
    have hw0 : 0 ≤ (1 + |x.2.1|) ^ w := by positivity
    have hmul := mul_le_mul_of_nonneg_left htot hw0
    have h1 := mul_le_mul_of_nonneg_left (hbQ x hx1 l' hl') (norm_nonneg LQ)
    have h2 := mul_le_mul_of_nonneg_left (hbE x hx1 l' hl') (norm_nonneg LE)
    have h3 := mul_le_mul_of_nonneg_left (hbA x hx1 l' hl') (norm_nonneg LA)
    have hC0_nn : 0 ≤ C₀ * x.2.2 ^ α := mul_nonneg hC₀ hrp0
    linarith

/-- `(x.2.2)⁻¹` belongs to `WtdProfJet m 0 0` on `1 ≤ x.2.2` for all `m : ℕ`. -/
theorem invAge_wtdProfJet : ∀ m : ℕ, WtdProfJet m 0 0 (fun x : ProfilePoint => (x.2.2)⁻¹)
  | 0 => by
    have hsm : ContDiffOn ℝ ∞ (fun x : ProfilePoint => (x.2.2)⁻¹) ageDomain :=
      (coordAge_wtdProfJet 0).1.inv fun x hx => ( hx : 0 < x.2.2).ne'
    refine ⟨hsm, 1, zero_le_one, fun x hx1 l hl => ?_⟩
    obtain rfl : l = 0 := Nat.eq_zero_of_le_zero hl
    rw [pow_zero, one_mul, Real.rpow_zero, mul_one, norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (zero_le_one.trans hx1)]
    exact inv_le_one_of_one_le₀ hx1
  | m + 1 => by
    have ih := invAge_wtdProfJet m
    have hsm : ContDiffOn ℝ ∞ (fun x : ProfilePoint => (x.2.2)⁻¹) ageDomain := ih.1
    have hdiff : ∀ x ∈ ageDomain, DifferentiableAt ℝ (fun y : ProfilePoint => (y.2.2)⁻¹) x :=
      fun x hx => (hsm.contDiffAt (B0185.isOpen_ageDomain.mem_nhds hx)).differentiableAt (by simp)
    have hQ : WtdProfJet m 0 0 (UnforcedLeray.B0184.partialQ (fun x : ProfilePoint => (x.2.2)⁻¹)) := by
      refine (WtdProfJet.zero m 0 0).congr fun x _ => ?_
      have hq : QConst (fun y : ProfilePoint => (y.2.2)⁻¹) := fun y t => by simp [eqDir]
      exact (hq.partialQ_eq_zero x).symm
    have hE : WtdProfJet m 0 0 (UnforcedLeray.B0184.partialEta (fun x : ProfilePoint => (x.2.2)⁻¹)) := by
      refine (WtdProfJet.zero m 0 0).congr fun x hx => ?_
      unfold UnforcedLeray.B0184.partialEta
      symm
      apply lhFderivLine (hdiff x hx)
      have hline : (fun t : ℝ => ((x + t • eηDir).2.2)⁻¹) = fun _ : ℝ => (x.2.2)⁻¹ := by
        funext t; simp [eηDir]
      rw [hline]
      exact hasDerivAt_const 0 (x.2.2)⁻¹
    have hA : WtdProfJet m 0 0 (UnforcedLeray.B0184.partialAge (fun x : ProfilePoint => (x.2.2)⁻¹)) := by
      have hprod : WtdProfJet m 0 0 (fun x : ProfilePoint => -((x.2.2)⁻¹ * (x.2.2)⁻¹)) := by
        simpa using (ih.mul ih).neg
      refine hprod.congr fun x hx => ?_
      unfold UnforcedLeray.B0184.partialAge
      symm
      apply lhFderivLine (hdiff x hx)
      have hline : (fun t : ℝ => ((x + t • esDir).2.2)⁻¹) = fun t : ℝ => (x.2.2 + t)⁻¹ := by
        funext t; simp [esDir]
      rw [hline]
      have hx0 : 0 < x.2.2 := hx
      have hg : HasDerivAt (fun t : ℝ => x.2.2 + t) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add x.2.2
      have hinv := hg.fun_inv (by linarith : x.2.2 + 0 ≠ 0)
      have hd_eq : -(1 : ℝ) / (x.2.2 + 0) ^ 2 = -((x.2.2)⁻¹ * (x.2.2)⁻¹) := by
        rw [add_zero]
        field_simp [hx0.ne']
      rwa [hd_eq] at hinv
    refine wtdProfJet_succ_of_partials hsm zero_le_one (fun x hx1 => ?_) hQ hE hA
    rw [pow_zero, one_mul, Real.rpow_zero, mul_one, abs_inv, abs_of_nonneg (zero_le_one.trans hx1)]
    exact inv_le_one_of_one_le₀ hx1

/-- Heat profile `lhP ν k` belongs to `WtdProfJet m w (w + m)` for `0 < ν ≤ 1` and all `m, w, k`. -/
theorem lhP_wtdProfJet {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ∀ (m w k : ℕ), WtdProfJet m w ((w : ℝ) + (m : ℝ)) (lhP ν k)
  | 0, w, k => by
    obtain ⟨C, hC0, hC⟩ := lhBound1D w k
    set B : ℝ := 2 ^ w * C * ν ^ (-(((k : ℝ) + 1) / 2))
    have hB0 : 0 ≤ B := by unfold B; positivity
    refine ⟨lhP_contDiffOn hν0 k, B, hB0, fun x hx1 l hl => ?_⟩
    obtain rfl : l = 0 := Nat.eq_zero_of_le_zero hl
    have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
    rw [Nat.cast_zero, add_zero, norm_iteratedFDeriv_zero, Real.norm_eq_abs, lhP_eq]
    have h_eta : 1 + |x.2.1| ≤ 2 * (1 + x.2.1 ^ 2) := by
      nlinarith [sq_nonneg (|x.2.1| - 1), sq_abs x.2.1, abs_nonneg x.2.1]
    have h_s : 1 + x.2.1 ^ 2 ≤ x.2.2 * (1 + x.2.1 ^ 2 / x.2.2) := by
      have heq : x.2.2 * (1 + x.2.1 ^ 2 / x.2.2) = x.2.2 + x.2.1 ^ 2 := by
        field_simp [hx0.ne']
      linarith
    have h_base : 1 + |x.2.1| ≤ 2 * x.2.2 * (1 + x.2.1 ^ 2 / x.2.2) := by linarith
    have h_pow : (1 + |x.2.1|) ^ w ≤
        2 ^ w * x.2.2 ^ (w : ℝ) * (1 + x.2.1 ^ 2 / x.2.2) ^ w := by
      calc (1 + |x.2.1|) ^ w
          ≤ (2 * x.2.2 * (1 + x.2.1 ^ 2 / x.2.2)) ^ w :=
            pow_le_pow_left₀ (by positivity) h_base w
        _ = 2 ^ w * x.2.2 ^ w * (1 + x.2.1 ^ 2 / x.2.2) ^ w := by rw [mul_pow, mul_pow]
        _ = 2 ^ w * x.2.2 ^ (w : ℝ) * (1 + x.2.1 ^ 2 / x.2.2) ^ w := by
            rw [Real.rpow_natCast]
    have h1D := hC ν hν0 hν1 x.2.2 hx1 x.2.1
    have hrp_split : (ν * x.2.2) ^ (-(((k : ℝ) + 1) / 2)) ≤ ν ^ (-(((k : ℝ) + 1) / 2)) := by
      rw [Real.mul_rpow hν0.le hx0.le]
      have hs_le : x.2.2 ^ (-(((k : ℝ) + 1) / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1
          (by linarith [Nat.cast_nonneg (α := ℝ) k] : -(((k : ℝ) + 1) / 2) ≤ 0)
      calc ν ^ (-(((k : ℝ) + 1) / 2)) * x.2.2 ^ (-(((k : ℝ) + 1) / 2))
          ≤ ν ^ (-(((k : ℝ) + 1) / 2)) * 1 :=
            mul_le_mul_of_nonneg_left hs_le (Real.rpow_nonneg hν0.le _)
        _ = ν ^ (-(((k : ℝ) + 1) / 2)) := mul_one _
    calc (1 + |x.2.1|) ^ w * |iteratedDeriv k (heatKernel1 (ν * x.2.2)) x.2.1|
        ≤ (2 ^ w * x.2.2 ^ (w : ℝ) * (1 + x.2.1 ^ 2 / x.2.2) ^ w) *
            |iteratedDeriv k (heatKernel1 (ν * x.2.2)) x.2.1| :=
          mul_le_mul_of_nonneg_right h_pow (abs_nonneg _)
      _ = 2 ^ w * x.2.2 ^ (w : ℝ) *
            ((1 + x.2.1 ^ 2 / x.2.2) ^ w * |iteratedDeriv k (heatKernel1 (ν * x.2.2)) x.2.1|) := by
          ring
      _ ≤ 2 ^ w * x.2.2 ^ (w : ℝ) * (C * (ν * x.2.2) ^ (-(((k : ℝ) + 1) / 2))) :=
          mul_le_mul_of_nonneg_left h1D (by positivity)
      _ ≤ 2 ^ w * x.2.2 ^ (w : ℝ) * (C * ν ^ (-(((k : ℝ) + 1) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrp_split hC0) (by positivity)
      _ = B * x.2.2 ^ (w : ℝ) := by unfold B; ring
  | m + 1, w, k => by
    have ih : ∀ w' k' : ℕ, WtdProfJet m w' ((w' : ℝ) + (m : ℝ)) (lhP ν k') :=
      fun w' k' => lhP_wtdProfJet hν0 hν1 m w' k'
    have hsm := lhP_contDiffOn hν0 k
    obtain ⟨_, C₀, hC₀, hb₀⟩ := (ih w k).mono_alpha
      (by push_cast; linarith : (w : ℝ) + (m : ℝ) ≤ (w : ℝ) + ((m + 1 : ℕ) : ℝ))
    have h0 : ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        (1 + |x.2.1|) ^ w * |lhP ν k x| ≤ C₀ * x.2.2 ^ ((w : ℝ) + ((m + 1 : ℕ) : ℝ)) := by
      intro x hx1
      have h := hb₀ x hx1 0 (Nat.zero_le m)
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have hQ : WtdProfJet m w ((w : ℝ) + ((m + 1 : ℕ) : ℝ))
        (UnforcedLeray.B0184.partialQ (lhP ν k)) :=
      (WtdProfJet.zero m w _).congr fun x _ =>
        ((QConst.lhP ν k).partialQ_eq_zero x).symm
    have hE : WtdProfJet m w ((w : ℝ) + ((m + 1 : ℕ) : ℝ))
        (UnforcedLeray.B0184.partialEta (lhP ν k)) :=
      ((ih w (k + 1)).mono_alpha (by push_cast; linarith)).congr fun x hx =>
        (lhPartialEta ν k hx).symm
    have hA : WtdProfJet m w ((w : ℝ) + ((m + 1 : ℕ) : ℝ))
        (UnforcedLeray.B0184.partialAge (lhP ν k)) := by
      have ht1 : WtdProfJet m w ((w : ℝ) + ((m + 1 : ℕ) : ℝ))
          (fun x => ((k : ℝ) + 1) * lhP ν k x) :=
        ((ih w k).const_mul ((k : ℝ) + 1)).mono_alpha (by push_cast; linarith)
      have ht2 : WtdProfJet m w ((w : ℝ) + ((m + 1 : ℕ) : ℝ))
          (fun x => x.2.1 * lhP ν (k + 1) x) := by
        have h := (ih (w + 1) (k + 1)).mul_eta
        have hexp : ((w + 1 : ℕ) : ℝ) + (m : ℝ) = (w : ℝ) + ((m + 1 : ℕ) : ℝ) := by
          push_cast; ring
        rwa [hexp] at h
      have hcomb : WtdProfJet m w ((w : ℝ) + ((m + 1 : ℕ) : ℝ))
          (fun x => -(2 : ℝ)⁻¹ * ((x.2.2)⁻¹ *
            (((k : ℝ) + 1) * lhP ν k x + x.2.1 * lhP ν (k + 1) x))) := by
        have hm := (invAge_wtdProfJet m).mul (ht1.add ht2)
        rw [zero_add, zero_add] at hm
        exact hm.const_mul (-(2 : ℝ)⁻¹)
      refine hcomb.congr fun x hx => ?_
      rw [lhPartialAge ν k hx]
      ring
    exact wtdProfJet_succ_of_partials hsm hC₀ h0 hQ hE hA

/-- `heatSumFam M ν c tr` has `WtdProfJet m w (w + m)` with age exponent independent of `M`! -/
theorem heatSumFam_wtdProfJet {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) (c : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (M m w : ℕ) :
    WtdProfJet m w ((w : ℝ) + (m : ℝ)) (heatSumFam M ν c tr) :=
  WtdProfJet.sum (Finset.range (M + 1)) fun j _ =>
    (lhP_wtdProfJet hν0 hν1 m w (2 * j)).const_mul (meanCoeff tr j)

/-! ### 3. One-sided half-ball Landau interpolation on `1 ≤ x.2.2` -/

private theorem rpow_two_sided_le (α : ℝ) {s t : ℝ} (hs1 : 1 ≤ s) (hst : s ≤ t)
    (ht2 : t ≤ 2 * s) :
    t ^ α ≤ max 1 (2 ^ α) * s ^ α := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
  have ht0 : 0 ≤ t := hs0.le.trans hst
  rcases le_total 0 α with hα | hα
  · calc t ^ α ≤ (2 * s) ^ α := Real.rpow_le_rpow ht0 ht2 hα
      _ = 2 ^ α * s ^ α := Real.mul_rpow zero_le_two hs0.le
      _ ≤ max 1 (2 ^ α) * s ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right 1 (2 ^ α)) (Real.rpow_nonneg hs0.le α)
  · calc t ^ α ≤ s ^ α := Real.rpow_le_rpow_of_nonpos hs0 hst hα
      _ = 1 * s ^ α := (one_mul _).symm
      _ ≤ max 1 (2 ^ α) * s ^ α :=
          mul_le_mul_of_nonneg_right (le_max_left 1 (2 ^ α)) (Real.rpow_nonneg hs0.le α)

/-- Single Landau-interpolation step on `1 ≤ y.2.2`: bounds `(1 + |η|)^w ‖D^{k+1} f(y)‖` from
`(1 + |η|)^{2w} ‖D^k f‖ ≤ C s^α` and unweighted `‖D^{k+2} f‖ ≤ M s^α`, valid for ANY `α : ℝ`. -/
private theorem wtdJetInterp_prof_step {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain)
    (k w : ℕ) (α : ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : ProfilePoint, 1 ≤ y.2.2 → ‖iteratedFDeriv ℝ (k + 2) f y‖ ≤ M * y.2.2 ^ α)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : ProfilePoint, 1 ≤ y.2.2 →
      (1 + |y.2.1|) ^ (2 * w) * ‖iteratedFDeriv ℝ k f y‖ ≤ C * y.2.2 ^ α) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ y : ProfilePoint, 1 ≤ y.2.2 →
      (1 + |y.2.1|) ^ w * ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ C' * y.2.2 ^ α := by
  set K_α : ℝ := max 1 (2 ^ α)
  have hKα0 : 0 ≤ K_α := zero_le_one.trans (le_max_left 1 (2 ^ α))
  set C' : ℝ := (2 * 4 ^ w * C + M) * K_α
  have hC'0 : 0 ≤ C' := mul_nonneg (add_nonneg (mul_nonneg (by positivity) hC0) hM0) hKα0
  refine ⟨C', hC'0, fun y hy1 => ?_⟩
  have hy0 : 0 < y.2.2 := lt_of_lt_of_le one_pos hy1
  have hy_rp0 : 0 ≤ y.2.2 ^ α := Real.rpow_nonneg hy0.le α
  have hGd : ∀ z : ProfilePoint, z ∈ ageDomain → DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z := by
    intro z hz
    have hc : ContDiffAt ℝ ∞ f z := hf.contDiffAt (B0185.isOpen_ageDomain.mem_nhds hz)
    exact (hc.iteratedFDeriv_right (m := 1) (i := k) (by exact_mod_cast le_top)).differentiableAt
      one_ne_zero
  have hHd : ∀ z : ProfilePoint, z ∈ ageDomain →
      DifferentiableAt ℝ (iteratedFDeriv ℝ (k + 1) f) z := by
    intro z hz
    have hc : ContDiffAt ℝ ∞ f z := hf.contDiffAt (B0185.isOpen_ageDomain.mem_nhds hz)
    exact (hc.iteratedFDeriv_right (m := 1) (i := k + 1) (by exact_mod_cast le_top)).differentiableAt
      one_ne_zero
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ProfilePoint) ℝ
  have hrel : ∀ z : ProfilePoint, fderiv ℝ (iteratedFDeriv ℝ k f) z =
      e (iteratedFDeriv ℝ (k + 1) f z) := by
    intro z
    have h := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := f) (n := k)) z
    simp only [Function.comp_apply] at h
    rw [h, LinearIsometryEquiv.apply_symm_apply]
  have hmapsub : ∀ a b : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => ProfilePoint) ℝ,
      e (a - b) = e a - e b := fun a b => e.toLinearEquiv.toLinearMap.map_sub a b
  set a : ℝ := (1 + |y.2.1|) ^ w with ha
  have ha1 : 1 ≤ a := one_le_pow₀ (by linarith [abs_nonneg y.2.1])
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
  set h : ℝ := a⁻¹ with hh
  have hh0 : 0 < h := inv_pos.2 ha0
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ ha1
  have hha : h * a = 1 := inv_mul_cancel₀ ha0.ne'
  set B : Set ProfilePoint :=
    ((univ : Set ℝ) ×ˢ ((univ : Set ℝ) ×ˢ Icc y.2.2 (2 * y.2.2))) ∩ Metric.closedBall y h
  have hBz : ∀ z ∈ B, y.2.2 ≤ z.2.2 ∧ z.2.2 ≤ 2 * y.2.2 ∧ dist z y ≤ h := by
    intro z hz
    rcases hz with ⟨⟨-, ⟨-, h1, h2⟩⟩, h3⟩
    exact ⟨h1, h2, Metric.mem_closedBall.mp h3⟩
  have hyB : y ∈ B :=
    ⟨⟨mem_univ _, ⟨mem_univ _, le_rfl, by linarith⟩⟩, Metric.mem_closedBall_self hh0.le⟩
  have hBconv : Convex ℝ B :=
    (convex_univ.prod (convex_univ.prod (convex_Icc _ _))).inter (convex_closedBall y h)
  set C_y : ℝ := C * K_α * y.2.2 ^ α
  set M_y : ℝ := M * K_α * y.2.2 ^ α
  have hMy0 : 0 ≤ M_y := mul_nonneg (mul_nonneg hM0 hKα0) hy_rp0
  have hGB : ∀ z ∈ B, a ^ 2 * ‖iteratedFDeriv ℝ k f z‖ ≤ 4 ^ w * C_y := by
    intro z hz
    obtain ⟨hz_lo, hz_hi, hzd⟩ := hBz z hz
    have hz1 : 1 ≤ z.2.2 := hy1.trans hz_lo
    have hzd' : ‖z - y‖ ≤ h := by rwa [dist_eq_norm] at hzd
    have hyz : ‖y - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hzd'.trans hh1
    have heta : |y.2.1 - z.2.1| ≤ 1 := by
      have h1 : |((y - z).2).1| ≤ ‖(y - z).2‖ := by
        simpa [Real.norm_eq_abs] using norm_fst_le (y - z).2
      have h2 : ‖(y - z).2‖ ≤ ‖y - z‖ := norm_snd_le (y - z)
      exact h1.trans (h2.trans hyz)
    have hWz : 1 + |y.2.1| ≤ 2 * (1 + |z.2.1|) := by
      have := abs_sub_abs_le_abs_sub y.2.1 z.2.1
      have := abs_nonneg z.2.1
      linarith
    have hapow : a ^ 2 ≤ 4 ^ w * (1 + |z.2.1|) ^ (2 * w) := by
      have e1 : a ^ 2 = (1 + |y.2.1|) ^ (2 * w) := by rw [ha, ← pow_mul, mul_comm]
      have e2 : (4 : ℝ) ^ w * (1 + |z.2.1|) ^ (2 * w) = (2 * (1 + |z.2.1|)) ^ (2 * w) := by
        rw [mul_pow, pow_mul (2 : ℝ) 2 w]; norm_num
      rw [e1, e2]
      exact pow_le_pow_left₀ (by positivity) hWz _
    have hz_rp : z.2.2 ^ α ≤ K_α * y.2.2 ^ α := rpow_two_sided_le α hy1 hz_lo hz_hi
    calc a ^ 2 * ‖iteratedFDeriv ℝ k f z‖
        ≤ (4 ^ w * (1 + |z.2.1|) ^ (2 * w)) * ‖iteratedFDeriv ℝ k f z‖ :=
          mul_le_mul_of_nonneg_right hapow (norm_nonneg _)
      _ = 4 ^ w * ((1 + |z.2.1|) ^ (2 * w) * ‖iteratedFDeriv ℝ k f z‖) := by ring
      _ ≤ 4 ^ w * (C * z.2.2 ^ α) := mul_le_mul_of_nonneg_left (hC z hz1) (by positivity)
      _ ≤ 4 ^ w * (C * (K_α * y.2.2 ^ α)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz_rp hC0) (by positivity)
      _ = 4 ^ w * C_y := by unfold C_y; ring
  have hbdH : ∀ x ∈ B, ‖fderiv ℝ (iteratedFDeriv ℝ (k + 1) f) x‖ ≤ M_y := by
    intro x hx
    obtain ⟨hx_lo, hx_hi, -⟩ := hBz x hx
    rw [norm_fderiv_iteratedFDeriv]
    calc ‖iteratedFDeriv ℝ (k + 2) f x‖
        ≤ M * x.2.2 ^ α := hM x (hy1.trans hx_lo)
      _ ≤ M * (K_α * y.2.2 ^ α) :=
          mul_le_mul_of_nonneg_left (rpow_two_sided_le α hy1 hx_lo hx_hi) hM0
      _ = M_y := by unfold M_y; ring
  have hHlip : ∀ z ∈ B,
      ‖iteratedFDeriv ℝ (k + 1) f z - iteratedFDeriv ℝ (k + 1) f y‖ ≤ M_y * ‖z - y‖ :=
    fun z hz => Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := iteratedFDeriv ℝ (k + 1) f) (s := B) (C := M_y)
      (fun x hx => hHd x (lt_of_lt_of_le hy0 (hBz x hx).1)) hbdH hBconv hyB hz
  have hGlip : ∀ z ∈ B,
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z - fderiv ℝ (iteratedFDeriv ℝ k f) y‖ ≤ M_y * ‖z - y‖ := by
    intro z hz
    rw [hrel z, hrel y, ← hmapsub, LinearIsometryEquiv.norm_map]
    exact hHlip z hz
  set L := fderiv ℝ (iteratedFDeriv ℝ k f) y with hLdef
  have hφfd : ∀ x ∈ B, ‖fderiv ℝ (fun z => iteratedFDeriv ℝ k f z - L z) x‖ ≤ M_y * h := by
    intro x hx
    rw [fderiv_fun_sub (hGd x (lt_of_lt_of_le hy0 (hBz x hx).1)) L.differentiableAt,
      ContinuousLinearMap.fderiv]
    have hxy : ‖x - y‖ ≤ h := by
      have := (hBz x hx).2.2
      rwa [dist_eq_norm] at this
    exact (hGlip x hx).trans (mul_le_mul_of_nonneg_left hxy hMy0)
  have hφmean : ∀ zh ∈ B,
      ‖(iteratedFDeriv ℝ k f zh - L zh) - (iteratedFDeriv ℝ k f y - L y)‖
        ≤ (M_y * h) * ‖zh - y‖ := fun zh hzh =>
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => iteratedFDeriv ℝ k f z - L z) (s := B) (C := M_y * h)
      (fun x hx => (hGd x (lt_of_lt_of_le hy0 (hBz x hx).1)).sub L.differentiableAt)
      hφfd hBconv hyB hzh
  have hcore : ∀ u : ProfilePoint, 0 ≤ u.2.2 → ‖u‖ ≤ 1 → a * ‖L u‖ ≤ C' * y.2.2 ^ α := by
    intro u hu0 hu1
    have hu_hi : u.2.2 ≤ 1 := by
      have h1 : |u.2.2| ≤ ‖u.2‖ := by simpa [Real.norm_eq_abs] using norm_snd_le u.2
      have h2 : ‖u.2‖ ≤ ‖u‖ := norm_snd_le u
      exact (le_abs_self _).trans (h1.trans (h2.trans hu1))
    have hzB : y + h • u ∈ B := by
      refine ⟨⟨mem_univ _, ⟨mem_univ _, ?_, ?_⟩⟩, ?_⟩
      · change y.2.2 ≤ y.2.2 + h * u.2.2
        linarith [mul_nonneg hh0.le hu0]
      · change y.2.2 + h * u.2.2 ≤ 2 * y.2.2
        have hhu : h * u.2.2 ≤ 1 := by
          calc h * u.2.2 ≤ 1 * 1 := mul_le_mul hh1 hu_hi hu0 zero_le_one
            _ = 1 := mul_one 1
        linarith
      · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos hh0]
        exact mul_le_of_le_one_right hh0.le hu1
    have hzy_norm : ‖y + h • u - y‖ ≤ h := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh0]
      exact mul_le_of_le_one_right hh0.le hu1
    have e_sub : (iteratedFDeriv ℝ k f (y + h • u) - L (y + h • u))
        - (iteratedFDeriv ℝ k f y - L y)
        = (iteratedFDeriv ℝ k f (y + h • u) - iteratedFDeriv ℝ k f y) - h • L u := by
      rw [map_add, map_smul]; abel
    have h3 : ‖(iteratedFDeriv ℝ k f (y + h • u) - iteratedFDeriv ℝ k f y) - h • L u‖
        ≤ M_y * h ^ 2 := by
      have hstep : ‖(iteratedFDeriv ℝ k f (y + h • u) - iteratedFDeriv ℝ k f y) - h • L u‖
          ≤ (M_y * h) * h := by
        rw [← e_sub]
        exact (hφmean _ hzB).trans
          (mul_le_mul_of_nonneg_left hzy_norm (mul_nonneg hMy0 hh0.le))
      have : (M_y * h) * h = M_y * h ^ 2 := by ring
      linarith
    have hsplit : h * ‖L u‖ ≤
        ‖iteratedFDeriv ℝ k f (y + h • u)‖ + ‖iteratedFDeriv ℝ k f y‖ + M_y * h ^ 2 := by
      have h4 := norm_sub_le (iteratedFDeriv ℝ k f (y + h • u) - iteratedFDeriv ℝ k f y)
        ((iteratedFDeriv ℝ k f (y + h • u) - iteratedFDeriv ℝ k f y) - h • L u)
      rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hh0] at h4
      have h5 := norm_sub_le (iteratedFDeriv ℝ k f (y + h • u)) (iteratedFDeriv ℝ k f y)
      linarith
    have hGzh := hGB _ hzB
    have hGy := hGB y hyB
    have hXd : a * ‖L u‖ = a ^ 2 * (h * ‖L u‖) := by
      calc a * ‖L u‖ = (h * a) * (a * ‖L u‖) := by rw [hha, one_mul]
        _ = a ^ 2 * (h * ‖L u‖) := by ring
    have hMd : a ^ 2 * (M_y * h ^ 2) = M_y := by
      calc a ^ 2 * (M_y * h ^ 2) = M_y * (h * a) ^ 2 := by ring
        _ = M_y := by rw [hha]; ring
    have hmul := mul_le_mul_of_nonneg_left hsplit (sq_nonneg a)
    have hexp : a ^ 2 * (‖iteratedFDeriv ℝ k f (y + h • u)‖ + ‖iteratedFDeriv ℝ k f y‖
        + M_y * h ^ 2) = a ^ 2 * ‖iteratedFDeriv ℝ k f (y + h • u)‖
          + a ^ 2 * ‖iteratedFDeriv ℝ k f y‖ + a ^ 2 * (M_y * h ^ 2) := by ring
    have hC'eq : 2 * 4 ^ w * C_y + M_y = C' * y.2.2 ^ α := by
      unfold C_y M_y C'; ring
    linarith
  have hsign : ∀ u : ProfilePoint, ‖u‖ ≤ 1 → a * ‖L u‖ ≤ C' * y.2.2 ^ α := by
    intro u hu
    rcases le_total 0 u.2.2 with h0 | h0
    · exact hcore u h0 hu
    · have h1 := hcore (-u) (by change 0 ≤ -u.2.2; linarith) (by rw [norm_neg]; exact hu)
      rwa [map_neg, norm_neg] at h1
  have hKnn : 0 ≤ C' * y.2.2 ^ α := mul_nonneg hC'0 hy_rp0
  have hall : ∀ u : ProfilePoint, ‖L u‖ ≤ ((C' * y.2.2 ^ α) / a) * ‖u‖ := by
    intro u
    by_cases hu : u = 0
    · rw [hu]; simp
    · have hc : 0 < ‖u‖ := norm_pos_iff.mpr hu
      set v : ProfilePoint := ‖u‖⁻¹ • u
      have hvn : ‖v‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hc.ne']
      have huv : u = ‖u‖ • v := by
        simp [v, smul_smul, mul_inv_cancel₀ hc.ne']
      have hLv : ‖L v‖ ≤ (C' * y.2.2 ^ α) / a := by
        rw [le_div_iff₀ ha0]
        linarith [hsign v hvn.le]
      calc ‖L u‖ = ‖u‖ * ‖L v‖ := by
            conv_lhs => rw [huv]
            rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ ‖u‖ * ((C' * y.2.2 ^ α) / a) := mul_le_mul_of_nonneg_left hLv hc.le
        _ = ((C' * y.2.2 ^ α) / a) * ‖u‖ := by ring
  have hLnorm : ‖L‖ ≤ (C' * y.2.2 ^ α) / a :=
    ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hKnn ha0.le) hall
  rw [← norm_fderiv_iteratedFDeriv, ← hLdef]
  calc a * ‖L‖ ≤ a * ((C' * y.2.2 ^ α) / a) := mul_le_mul_of_nonneg_left hLnorm ha0.le
    _ = C' * y.2.2 ^ α := by field_simp [ha0.ne']

/-- Iterated Landau interpolation for a single derivative order `k`. -/
private theorem wtdJetInterp_prof_order {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain)
    (α : ℝ) :
    ∀ (k w : ℕ) {C₀ C_u : ℝ}, 0 ≤ C₀ → 0 ≤ C_u →
      (∀ y : ProfilePoint, 1 ≤ y.2.2 → (1 + |y.2.1|) ^ (2 ^ k * w) * |f y| ≤ C₀ * y.2.2 ^ α) →
      (∀ y : ProfilePoint, 1 ≤ y.2.2 → ∀ j ≤ k + 1,
        ‖iteratedFDeriv ℝ j f y‖ ≤ C_u * y.2.2 ^ α) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ProfilePoint, 1 ≤ y.2.2 →
        (1 + |y.2.1|) ^ w * ‖iteratedFDeriv ℝ k f y‖ ≤ C * y.2.2 ^ α
  | 0, w, C₀, _, hC₀, _, h0, _ => by
    refine ⟨C₀, hC₀, fun y hy1 => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    simpa using h0 y hy1
  | k + 1, w, C₀, C_u, hC₀, hCu, h0, hu => by
    have h0' : ∀ y : ProfilePoint, 1 ≤ y.2.2 →
        (1 + |y.2.1|) ^ (2 ^ k * (2 * w)) * |f y| ≤ C₀ * y.2.2 ^ α := by
      have heq : 2 ^ k * (2 * w) = 2 ^ (k + 1) * w := by ring
      rw [heq]
      exact h0
    have hu' : ∀ y : ProfilePoint, 1 ≤ y.2.2 → ∀ j ≤ k + 1,
        ‖iteratedFDeriv ℝ j f y‖ ≤ C_u * y.2.2 ^ α :=
      fun y hy1 j hj => hu y hy1 j (hj.trans (Nat.le_succ _))
    obtain ⟨Ck, hCk0, hCk⟩ := wtdJetInterp_prof_order hf α k (2 * w) hC₀ hCu h0' hu'
    exact wtdJetInterp_prof_step hf k w α hCu (fun y hy1 => hu y hy1 (k + 2) le_rfl) hCk0 hCk

/-- **Weighted `ProfilePoint` jet bound from order-`0` weighted decay + unweighted jets**:
if `f` is `C^∞` on `ageDomain`, satisfies `(1 + |η|)^{2^m w} |f(x)| ≤ C₀ s^α` on `1 ≤ s`, and has
unweighted Fréchet derivatives `‖D^j f(x)‖ ≤ C_u s^α` for `j ≤ m + 1` on `1 ≤ s`, then
`WtdProfJet m w α f` holds (for ANY `α : ℝ`, positive, zero, or negative). -/
theorem wtdProfJet_of_zero_and_unweighted {m w : ℕ} {α : ℝ} {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain)
    {C₀ C_u : ℝ} (hC₀ : 0 ≤ C₀) (hCu : 0 ≤ C_u)
    (h0 : ∀ x : ProfilePoint, 1 ≤ x.2.2 →
      (1 + |x.2.1|) ^ (2 ^ m * w) * |f x| ≤ C₀ * x.2.2 ^ α)
    (hu : ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ j ≤ m + 1,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C_u * x.2.2 ^ α) :
    WtdProfJet m w α f := by
  have h_each : ∀ l ≤ m, ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ x : ProfilePoint, 1 ≤ x.2.2 →
      (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f x‖ ≤ Cl * x.2.2 ^ α := by
    intro l hl
    have h0_l : ∀ x : ProfilePoint, 1 ≤ x.2.2 →
        (1 + |x.2.1|) ^ (2 ^ l * w) * |f x| ≤ C₀ * x.2.2 ^ α := by
      intro x hx1
      have hle_exp : 2 ^ l * w ≤ 2 ^ m * w :=
        Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num) hl)
      have h1 : 1 ≤ 1 + |x.2.1| := by linarith [abs_nonneg x.2.1]
      exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 hle_exp) (abs_nonneg _)).trans
        (h0 x hx1)
    have hu_l : ∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ j ≤ l + 1,
        ‖iteratedFDeriv ℝ j f x‖ ≤ C_u * x.2.2 ^ α :=
      fun x hx1 j hj => hu x hx1 j (hj.trans (Nat.succ_le_succ hl))
    exact wtdJetInterp_prof_order hf α l w hC₀ hCu h0_l hu_l
  choose C_fn hC_fn using fun l : Fin (m + 1) => h_each l.1 (Nat.lt_succ_iff.1 l.2)
  refine ⟨hf, ∑ l : Fin (m + 1), C_fn l, Finset.sum_nonneg fun l _ => (hC_fn l).1,
    fun x hx1 l hl => ?_⟩
  let l_fin : Fin (m + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
  have hx0 : 0 < x.2.2 := lt_of_lt_of_le one_pos hx1
  have hle_sum : C_fn l_fin ≤ ∑ i : Fin (m + 1), C_fn i :=
    Finset.single_le_sum (fun i _ => (hC_fn i).1) (Finset.mem_univ l_fin)
  exact ((hC_fn l_fin).2 x hx1).trans
    (mul_le_mul_of_nonneg_right hle_sum (Real.rpow_nonneg hx0.le α))

end UnforcedLeray.Short.IIb.RawResidualIteratedLateTailAux

