import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1.EarlyJet2
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_R06
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.TrainStreamWtdBdd_Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.WtdJetInterp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.MeanJetsFixed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1.MeanJetFormula
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1_2.PsiJetInterior
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Mean

/-!
# `PartII-b:S2/1/2/1`: `ResProfileEarlyJetAll` (fixed-threshold early-age residual chart jets)

Source of record: `the November 2 reference manuscript`, lines 429–467, 494–496,
1294–1304, 2542–2548.

Proves `resProfileEarlyJetAll_proof : UnforcedLeray.Short.IIb.ResProfileEarlyJetAll`:
at a single viscosity threshold `ν₀ > 0` independent of derivative order `L` and transverse weight
exponent `N`:
1. `trainStreamWtdBdd_fixed` bounds `(1 + |η|)^w ‖D^i ψ(s, q, η)‖` on `0 < s ≤ 1` for all `w, i`
   from `fluctDoubledWeightPoly_proof` (`PartII-b:S2/wtd/fluct`), `PartI.trainFluctAgeJetFixed`,
   `PartI.trainJetsBoundedFixed`, and `wtdJetInterp`.
2. `trainPressureWtdBdd_fixed` bounds `(1 + |η|)^w ‖D^i p(s, q, η)‖` on `0 < s ≤ 1` for all `w, i`
   by combining the fixed-threshold unweighted pressure Fréchet jets (`PartIIa.trainVelPressAgeJetFixed`
   + `PartI.jointFromAgeJets`) on `0 < s ≤ 2` with the order-`0` weighted transverse pressure tail
   (`PartI.trainTransverseTails_proof` at `ℓ = j = 0`, `S_* = 2`) via unit-patch interpolation
   `wtdJetInterp`.
3. Pulling back to `ProfilePoint` (`EarlyAll`) and propagating through the five polynomial residual
   coefficients `coeffA₁, coeffA₂, coeffB₁, coeffB₂, coeffB₃` (`EarlyJet2Sub.resPolyMerid`) yields
   `(1 + |m.2.2|)^N ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) m‖ ≤ C` on `0 < m.1 ≤ 1`
   for all `l ≤ L`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190
open UnforcedLeray.Short.PartI
open UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.FarDecaySub
open UnforcedLeray.Short.PartIIIb.Concrete.EarlyJet2Sub

namespace UnforcedLeray.Short.IIb.EarlyJetAllAux

/-! ### 1. Early-age (`0 < x.2.2 ≤ 1`) weighted Fréchet-jet calculus on `ProfilePoint` -/

/-- Smooth profile on `ageDomain = {x | 0 < x.2.2}` whose `(1 + |x.2.1|)^w`-weighted Fréchet
derivatives of orders `≤ m` are bounded on `0 < x.2.2 ≤ 1`. -/
def EarlyWtdJet (m w : ℕ) (f : ProfilePoint → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f ageDomain ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ProfilePoint, 0 < x.2.2 → x.2.2 ≤ 1 → ∀ l ≤ m,
      (1 + |x.2.1|) ^ w * ‖iteratedFDeriv ℝ l f x‖ ≤ C

/-- Smooth profile belonging to `EarlyWtdJet m w` for all derivative orders `m` and weights `w`. -/
def EarlyAll (f : ProfilePoint → ℝ) : Prop :=
  ∀ m w : ℕ, EarlyWtdJet m w f

theorem EarlyWtdJet.congr {m w : ℕ} {f g : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w f) (hfg : EqOn f g ageDomain) :
    EarlyWtdJet m w g := by
  obtain ⟨hsm, C, hC0, hbd⟩ := hf
  refine ⟨hsm.congr hfg.symm, C, hC0, fun x hx0 hx1 l hl => ?_⟩
  have hev : g =ᶠ[𝓝 x] f :=
    Filter.eventuallyEq_of_mem (B0185.isOpen_ageDomain.mem_nhds hx0) (fun y hy => (hfg hy).symm)
  rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds]
  exact hbd x hx0 hx1 l hl

theorem EarlyWtdJet.mono_m {m m' w : ℕ} {f : ProfilePoint → ℝ}
    (hm : m' ≤ m) (hf : EarlyWtdJet m w f) :
    EarlyWtdJet m' w f :=
  ⟨hf.1, let ⟨C, hC0, hbd⟩ := hf.2; ⟨C, hC0, fun x hx0 hx1 l hl => hbd x hx0 hx1 l (hl.trans hm)⟩⟩

theorem EarlyWtdJet.mono_w {m w w' : ℕ} {f : ProfilePoint → ℝ}
    (hw : w' ≤ w) (hf : EarlyWtdJet m w f) :
    EarlyWtdJet m w' f := by
  obtain ⟨hsm, C, hC0, hbd⟩ := hf
  refine ⟨hsm, C, hC0, fun x hx0 hx1 l hl => ?_⟩
  have h1 : 1 ≤ 1 + |x.2.1| := by linarith [abs_nonneg x.2.1]
  have hpow : (1 + |x.2.1|) ^ w' ≤ (1 + |x.2.1|) ^ w := pow_le_pow_right₀ h1 hw
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hbd x hx0 hx1 l hl)

theorem EarlyWtdJet.add {m w : ℕ} {f g : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w f) (hg : EarlyWtdJet m w g) :
    EarlyWtdJet m w (fun x => f x + g x) := by
  obtain ⟨cf, Cf, hCf0, hbf⟩ := hf
  obtain ⟨cg, Cg, hCg0, hbg⟩ := hg
  refine ⟨cf.add cg, Cf + Cg, add_nonneg hCf0 hCg0, fun x hx0 hx1 l hl => ?_⟩
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
    _ ≤ Cf + Cg := add_le_add (hbf x hx0 hx1 l hl) (hbg x hx0 hx1 l hl)

theorem EarlyWtdJet.const_mul {m w : ℕ} (c : ℝ) {f : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w f) :
    EarlyWtdJet m w (fun x => c * f x) := by
  obtain ⟨cf, C, hC0, hbf⟩ := hf
  set L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ c
  refine ⟨contDiffOn_const.mul cf, ‖L‖ * C, mul_nonneg (norm_nonneg _) hC0, fun x hx0 hx1 l hl => ?_⟩
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
    _ ≤ ‖L‖ * C := mul_le_mul_of_nonneg_left (hbf x hx0 hx1 l hl) (norm_nonneg _)

theorem EarlyWtdJet.neg {m w : ℕ} {f : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w f) :
    EarlyWtdJet m w (fun x => -f x) := by
  have h := hf.const_mul (-1)
  have heq : (fun x : ProfilePoint => (-1 : ℝ) * f x) = fun x => -f x := by
    funext x; ring
  rwa [heq] at h

theorem EarlyWtdJet.sub {m w : ℕ} {f g : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w f) (hg : EarlyWtdJet m w g) :
    EarlyWtdJet m w (fun x => f x - g x) := by
  have h := hf.add hg.neg
  have heq : (fun x : ProfilePoint => f x + -g x) = fun x => f x - g x :=
    funext fun x => (sub_eq_add_neg (f x) (g x)).symm
  rwa [heq] at h

private theorem contDiffOn_fderiv_ageDomain {f : ProfilePoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (fderiv ℝ f) ageDomain := by
  have hw : ContDiffOn ℝ ∞ (fderivWithin ℝ f ageDomain) ageDomain :=
    hf.fderivWithin B0185.isOpen_ageDomain.uniqueDiffOn (m := ∞) (by simp)
  exact hw.congr fun y hy => (fderivWithin_of_isOpen B0185.isOpen_ageDomain hy).symm

theorem EarlyWtdJet.dirDeriv {m w : ℕ} (v : ProfilePoint) {f : ProfilePoint → ℝ}
    (hf : EarlyWtdJet (m + 1) w f) :
    EarlyWtdJet m w (fun x => fderiv ℝ f x v) := by
  obtain ⟨cf, C, hC0, hbf⟩ := hf
  set L : (ProfilePoint →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have cfd : ContDiffOn ℝ ∞ (fderiv ℝ f) ageDomain := contDiffOn_fderiv_ageDomain cf
  have cdir : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) ageDomain :=
    L.contDiff.comp_contDiffOn cfd
  refine ⟨cdir, ‖L‖ * C, mul_nonneg (norm_nonneg L) hC0, fun x hx0 hx1 l hl => ?_⟩
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
    _ ≤ ‖L‖ * C :=
        mul_le_mul_of_nonneg_left (hbf x hx0 hx1 (l + 1) (Nat.succ_le_succ hl)) (norm_nonneg L)

theorem EarlyWtdJet.mul {m w₁ w₂ : ℕ} {f g : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w₁ f) (hg : EarlyWtdJet m w₂ g) :
    EarlyWtdJet m (w₁ + w₂) (fun x => f x * g x) := by
  obtain ⟨cf, Cf, hCf0, hbf⟩ := hf
  obtain ⟨cg, Cg, hCg0, hbg⟩ := hg
  set B_comb : ℝ := ∑ l ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)
  have hBc0 : 0 ≤ B_comb :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨cf.mul cg, B_comb * Cf * Cg, mul_nonneg (mul_nonneg hBc0 hCf0) hCg0,
    fun x hx0 hx1 l hl => ?_⟩
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
    _ ≤ ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) * (Cf * Cg) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : i ≤ m := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hl
        have hli_le : l - i ≤ m := (Nat.sub_le l i).trans hl
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hbf x hx0 hx1 i hi_le) (hbg x hx0 hx1 (l - i) hli_le)
            (by positivity) hCf0)
          (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (Cf * Cg) := by
        rw [← Finset.sum_mul]
    _ ≤ B_comb * Cf * Cg := by
        calc (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (Cf * Cg)
            ≤ B_comb * (Cf * Cg) := mul_le_mul_of_nonneg_right hl_sub (mul_nonneg hCf0 hCg0)
          _ = B_comb * Cf * Cg := by ring

private theorem norm_iteratedFDeriv_clm_le (L : ProfilePoint →L[ℝ] ℝ) (x : ProfilePoint) :
    ∀ i : ℕ, ‖iteratedFDeriv ℝ i L x‖ ≤ if i = 0 then |L x| else if i = 1 then ‖L‖ else 0
  | 0 => by simp [norm_iteratedFDeriv_zero]
  | 1 => by simp [norm_iteratedFDeriv_one, L.fderiv]
  | j + 2 => by
    rw [← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (fun y => L y) = fun _ : ProfilePoint => L :=
      funext fun _ => L.fderiv
    rw [hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) L]
    simp

theorem coordAge_earlyWtdJet (m : ℕ) :
    EarlyWtdJet m 0 (fun x : ProfilePoint => x.2.2) := by
  set πAge : ProfilePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  refine ⟨πAge.contDiff.contDiffOn, max 1 ‖πAge‖, by positivity, fun x hx0 hx1 l _ => ?_⟩
  rw [pow_zero, one_mul]
  have hclm := norm_iteratedFDeriv_clm_le πAge x l
  have hx_eq : πAge x = x.2.2 := rfl
  rcases l with _ | _ | j
  · simp only [↓reduceIte, hx_eq, abs_of_pos hx0] at hclm
    exact hclm.trans (hx1.trans (le_max_left 1 ‖πAge‖))
  · simp only [Nat.succ_ne_zero, ↓reduceIte] at hclm
    exact hclm.trans (le_max_right 1 ‖πAge‖)
  · have hj0 : j + 2 ≠ 0 := by omega
    have hj1 : j + 2 ≠ 1 := by omega
    simp only [hj0, hj1, ↓reduceIte] at hclm
    exact hclm.trans (by positivity)

theorem EarlyWtdJet.mul_age {m w : ℕ} {f : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m w f) :
    EarlyWtdJet m w (fun x => x.2.2 * f x) := by
  have h := (coordAge_earlyWtdJet m).mul hf
  rwa [zero_add] at h

theorem EarlyWtdJet.mul_eta {m w : ℕ} {f : ProfilePoint → ℝ}
    (hf : EarlyWtdJet m (w + 1) f) :
    EarlyWtdJet m w (fun x => x.2.1 * f x) := by
  obtain ⟨cf, C, hC0, hbf⟩ := hf
  set πEta : ProfilePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  set K_π : ℝ := max 1 ‖πEta‖
  have hKπ : 0 ≤ K_π := by unfold K_π; positivity
  set B_comb : ℝ := ∑ l ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)
  have hBc0 : 0 ≤ B_comb :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨πEta.contDiff.contDiffOn.mul cf, B_comb * K_π * C,
    mul_nonneg (mul_nonneg hBc0 hKπ) hC0, fun x hx0 hx1 l hl => ?_⟩
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
    _ ≤ ∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ) * (K_π * C) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbf x hx0 hx1 (l - i) ((Nat.sub_le l i).trans hl)) hKπ)
          (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (K_π * C) := by
        rw [← Finset.sum_mul]
    _ ≤ B_comb * K_π * C := by
        calc (∑ i ∈ Finset.range (l + 1), (Nat.choose l i : ℝ)) * (K_π * C)
            ≤ B_comb * (K_π * C) := mul_le_mul_of_nonneg_right hl_sub (mul_nonneg hKπ hC0)
          _ = B_comb * K_π * C := by ring

theorem EarlyAll.congr {f g : ProfilePoint → ℝ} (hf : EarlyAll f) (hfg : EqOn f g ageDomain) :
    EarlyAll g :=
  fun m w => (hf m w).congr hfg

theorem EarlyAll.add {f g : ProfilePoint → ℝ} (hf : EarlyAll f) (hg : EarlyAll g) :
    EarlyAll (fun x => f x + g x) :=
  fun m w => (hf m w).add (hg m w)

theorem EarlyAll.sub {f g : ProfilePoint → ℝ} (hf : EarlyAll f) (hg : EarlyAll g) :
    EarlyAll (fun x => f x - g x) :=
  fun m w => (hf m w).sub (hg m w)

theorem EarlyAll.neg {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (fun x => -f x) :=
  fun m w => (hf m w).neg

theorem EarlyAll.const_mul (c : ℝ) {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (fun x => c * f x) :=
  fun m w => (hf m w).const_mul c

theorem EarlyAll.mul {f g : ProfilePoint → ℝ} (hf : EarlyAll f) (hg : EarlyAll g) :
    EarlyAll (fun x => f x * g x) := by
  intro m w
  have h := (hf m w).mul (hg m 0)
  rwa [Nat.add_zero] at h

theorem EarlyAll.partialQ {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (UnforcedLeray.B0184.partialQ f) :=
  fun m w => (hf (m + 1) w).dirDeriv eqDir

theorem EarlyAll.partialEta {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (UnforcedLeray.B0184.partialEta f) :=
  fun m w => (hf (m + 1) w).dirDeriv eηDir

theorem EarlyAll.partialAge {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (UnforcedLeray.B0184.partialAge f) :=
  fun m w => (hf (m + 1) w).dirDeriv esDir

theorem EarlyAll.ageOp {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (ageOperator f) := by
  intro m w
  have h1 : EarlyWtdJet m w (fun x => x.2.1 * UnforcedLeray.B0184.partialEta f x) :=
    (hf.partialEta m (w + 1)).mul_eta
  have h2 : EarlyWtdJet m w (fun x => 2 * (x.2.2 * UnforcedLeray.B0184.partialAge f x)) :=
    ((hf.partialAge m w).mul_age).const_mul 2
  refine (h1.add h2).congr fun x _ => ?_
  unfold ageOperator
  ring

theorem EarlyAll.ageShift (a : ℝ) {f : ProfilePoint → ℝ} (hf : EarlyAll f) :
    EarlyAll (UnforcedLeray.B0188.ageShift a f) := by
  refine (hf.ageOp.add (hf.const_mul a)).congr fun x _ => ?_
  unfold UnforcedLeray.B0188.ageShift
  ring

/-! ### 2. Closure of the five polynomial residual coefficients under `EarlyAll` -/

theorem earlyAll_coeffA1 (ν : ℝ) {ψ pr : ProfilePoint → ℝ}
    (hψ : EarlyAll ψ) (hp : EarlyAll pr) :
    EarlyAll (coeffA₁ ν ψ pr) := by
  have hv1 : EarlyAll (streamV1 ψ) := hψ.partialEta.neg
  have hH : EarlyAll (ageDefect ψ) := hψ.sub hψ.ageOp
  have hW :=
    (((((hv1.mul hv1.ageOp).neg).add (hH.mul hv1.partialEta)).sub (hv1.mul hv1)).add
      ((hv1.partialQ.ageShift 1).const_mul (2 * ν))).sub (hp.ageShift 2)
  refine hW.congr fun x _ => ?_
  simp only [coeffA₁, ageDefect, ageShift, streamV1]
  ring

theorem earlyAll_coeffA2 (ν : ℝ) {ψ : ProfilePoint → ℝ} (hψ : EarlyAll ψ) :
    EarlyAll (coeffA₂ ν ψ) := by
  have hv1 : EarlyAll (streamV1 ψ) := hψ.partialEta.neg
  have hv2 : EarlyAll (streamV2 ψ) := hψ.partialQ
  have hH : EarlyAll (ageDefect ψ) := hψ.sub hψ.ageOp
  have hlap := hH.partialQ.partialQ.add hH.partialEta.partialEta
  have hTD := ((hH.partialAge.add (hv1.mul hH.partialQ)).add (hv2.mul hH.partialEta)).sub
    (hlap.const_mul ν)
  have hW := ((hTD.add (hH.mul hv2.partialEta)).sub (hv1.mul (hv2.ageShift 1))).add
    ((hv2.partialQ.ageShift 1).const_mul (2 * ν))
  refine hW.congr fun x _ => ?_
  simp only [coeffA₂, transportDiffusion, profileLap, streamV1, streamV2, ageDefect, ageShift]

theorem earlyAll_coeffB1 (ν : ℝ) {ψ : ProfilePoint → ℝ} (hψ : EarlyAll ψ) :
    EarlyAll (coeffB₁ ν ψ) := by
  have hv1 : EarlyAll (streamV1 ψ) := hψ.partialEta.neg
  refine (((hv1.ageShift 2).ageOp).const_mul (-ν)).congr fun x _ => ?_
  simp only [coeffB₁]

theorem earlyAll_coeffB2 (ν : ℝ) {ψ : ProfilePoint → ℝ} (hψ : EarlyAll ψ) :
    EarlyAll (coeffB₂ ν ψ) := by
  have hv1 : EarlyAll (streamV1 ψ) := hψ.partialEta.neg
  have hv2 : EarlyAll (streamV2 ψ) := hψ.partialQ
  have hH : EarlyAll (ageDefect ψ) := hψ.sub hψ.ageOp
  have hW := ((((hv1.mul (hH.ageShift 1)).neg).add (hH.mul hH.partialEta)).add
    ((hH.partialQ.ageShift 1).const_mul (2 * ν))).sub
    (((hv2.ageShift 1).ageShift 1).const_mul ν)
  refine hW.congr fun x _ => ?_
  simp only [coeffB₂, streamV1, streamV2, ageDefect, ageShift]

theorem earlyAll_coeffB3 (ν : ℝ) {ψ : ProfilePoint → ℝ} (hψ : EarlyAll ψ) :
    EarlyAll (coeffB₃ ν ψ) := by
  have hH : EarlyAll (ageDefect ψ) := hψ.sub hψ.ageOp
  refine ((((hH.ageShift 1).ageShift 1).const_mul (-ν))).congr fun x _ => ?_
  simp only [coeffB₃]

/-! ### 3. Fixed-threshold stream and pressure `EarlyAll` bounds -/

private theorem partI_transverseTails : PartI.TrainTransverseTails := by
  have hFD0 : PartI.OverlapFluctuationDecay :=
    PartI.overlap_fluctuation_decay PartI.overlap_highnorm_uniform
  have hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof hFD0
      (PartI.overlap_mean_decay PartI.overlap_highnorm_uniform hFD0 PartI.overlap_mean_primitive)
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  exact PartI.trainTransverseTails_proof hVort hTails

private theorem trainFluctWtdAgeJet_fixed : TrainFluctWtdAgeJet := by
  have hW : WeightedTrainFluctAgeJetFixed :=
    weightedTrainFluctAgeJetFixed_of PartI.trainFluctAgeJetFixed
      UnforcedLeray.Short.IIb.fluctDoubledWeightPoly_proof
  intro ρ hρ
  obtain ⟨ν₀, hν₀, h'⟩ := hW ρ hρ
  refine ⟨ν₀, hν₀, fun ν c hν hle hc tr htr m ℓ j S => ?_⟩
  subst hc
  obtain ⟨C, κ, hκ, hC⟩ := h' ν hν hle tr htr m ℓ j
  refine ⟨|C|, fun s hs _ z => ?_⟩
  have he0 : 0 ≤ Real.exp (-(κ * s)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(κ * s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hκ.le hs.le))
  calc (1 + |z.2|) ^ m * ‖PartI.ageJet ℓ j
          (fun r w => tr.ψ r w - PartI.hmean (PartI.trainPeriod ρ ν) (tr.ψ r) w.2) s z‖
      ≤ C * Real.exp (-(κ * s)) := hC s hs z
    _ ≤ |C| * Real.exp (-(κ * s)) := mul_le_mul_of_nonneg_right (le_abs_self C) he0
    _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) he1

theorem trainStreamWtdBdd_fixed : TrainStreamWtdBdd :=
  trainStreamWtdBdd_of (trainFluctWtdBdd_of trainFluctWtdAgeJet_fixed)
    (trainMeanWtdBdd_of
      (trainMeanWtdMixed_of (psiJetWtd_of partI_transverseTails _root_.psiJetInterior)
        meanJetFormula)
      (meanJetsFixed_of PartI.trainJetsBoundedFixed) wtdJetInterp)

/-- Fixed-threshold weighted Fréchet-jet bound on `0 < y.1 ≤ 1` for the planar train pressure
`tr.p`, proved by unit-patch interpolation `wtdJetInterp` between the fixed-threshold unweighted
pressure Fréchet jets (`PartIIa.trainVelPressAgeJetFixed` + `PartI.jointFromAgeJets`) and the
order-`0` transverse tail (`partI_transverseTails` at `ℓ = j = 0`, `S_* = 2`). -/
theorem trainPressureWtdBdd_fixed :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (PartI.trainPeriod 2 ν), PartI.IsBUCTrain tr →
        ∀ m i : ℕ, ∃ C : ℝ, ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 →
          (1 + |y.2.2|) ^ m *
            ‖iteratedFDeriv ℝ i (fun x : ℝ × Plane => tr.p x.1 x.2) y‖ ≤ C := by
  have hρ2 : (1 : ℝ) / 2 < 2 := by norm_num
  obtain ⟨b_T, C₀_T, C'_T, hb_T, hC₀_T, hC'_T, C₁_T, N₁_T, ν_tail, hC₁_T, hν_tail, hTail⟩ :=
    partI_transverseTails 2 hρ2 0 0
  obtain ⟨ν_vp, hν_vp, hVP⟩ := PartIIa.trainVelPressAgeJetFixed 2 hρ2
  refine ⟨min ν_tail ν_vp, lt_min hν_tail hν_vp, fun ν hν hν_le tr htr => ?_⟩
  have hν_tail_le : ν ≤ ν_tail := hν_le.trans (min_le_left _ _)
  have hν_vp_le : ν ≤ ν_vp := hν_le.trans (min_le_right _ _)
  have hsm : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hAge := (hVP ν hν hν_vp_le tr htr).2
  set π2 : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hπ2 : ‖π2‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    exact norm_snd_le z
  have hUnw : ∀ k : ℕ, 1 ≤ k → ∃ M : ℝ, ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 + 1 →
      ‖iteratedFDeriv ℝ k (fun x : ℝ × Plane => tr.p x.1 x.2) y‖ ≤ M := by
    intro k _hk
    obtain ⟨K, hK0, hJ⟩ := PartI.jointFromAgeJets k
    choose Cℓ κℓ hCℓ hκℓ hbdℓ using fun ℓ : ℕ => hAge ℓ (k - ℓ)
    refine ⟨K * ∑ ℓ ∈ Finset.range (k + 1), Cℓ ℓ, fun y hy0 _hy2 => ?_⟩
    have hmain := hJ tr.p hsm y hy0
    have hsum : ∑ ℓ ∈ Finset.range (k + 1), ‖PartI.ageJet ℓ (k - ℓ) tr.p y.1 y.2‖ ≤
        ∑ ℓ ∈ Finset.range (k + 1), Cℓ ℓ := by
      refine Finset.sum_le_sum fun ℓ _ => ?_
      have he1 : Real.exp (-(κℓ ℓ * y.1)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (hκℓ ℓ).le hy0.le))
      exact (hbdℓ ℓ y.1 hy0 y.2).trans (mul_le_of_le_one_right (hCℓ ℓ).le he1)
    exact hmain.trans (mul_le_mul_of_nonneg_left hsum hK0)
  have hW0 : ∀ w : ℕ, ∃ C : ℝ, ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 + 1 →
      (1 + |π2 y.2|) ^ w * |tr.p y.1 y.2| ≤ C := by
    intro w
    obtain ⟨C00, κ00, hC00, hκ00, hbd00⟩ := hAge 0 0
    let c : ℝ := PartI.trainPeriod 2 ν
    have hc0 : 0 < c := Real.rpow_pos_of_pos hν _
    set A_reg : ℝ := 4 + C'_T / ν
    have hA_reg : 0 < A_reg := by unfold A_reg; positivity
    set γ : ℝ := min (b_T / c) (b_T / (C₀_T + ν * 2))
    have hγ : 0 < γ := by unfold γ; positivity
    set P2 : ℝ := PartI.polyPS C₁_T N₁_T ν c 2
    have hP2_nn : 0 ≤ P2 := by
      unfold P2 PartI.polyPS
      have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      positivity
    set K_fac : ℝ := (w.factorial : ℝ) * (γ ^ w)⁻¹
    have hK_fac : 0 < K_fac := by
      unfold K_fac
      have hfac : (0 : ℝ) < w.factorial := by exact_mod_cast w.factorial_pos
      positivity
    refine ⟨max (A_reg ^ w * C00) (2 * A_reg ^ w * P2 * K_fac), fun y hy0 hy2 => ?_⟩
    change (1 + |y.2.2|) ^ w * |tr.p y.1 y.2| ≤ _
    rcases le_or_gt |y.2.2| (C'_T / ν + 3) with hη | hη
    · have hw_le : (1 + |y.2.2|) ^ w ≤ A_reg ^ w := by
        refine pow_le_pow_left₀ (by positivity) ?_ w
        unfold A_reg; linarith
      have hp_le : |tr.p y.1 y.2| ≤ C00 := by
        have h0 := hbd00 y.1 hy0 y.2
        rw [PartI.norm_ageJet_zero_zero] at h0
        have he1 : Real.exp (-(κ00 * y.1)) ≤ 1 :=
          Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hκ00.le hy0.le))
        exact h0.trans (mul_le_of_le_one_right hC00.le he1)
      exact (mul_le_mul hw_le hp_le (abs_nonneg _) (by positivity)).trans (le_max_left _ _)
    · set l : ℝ := |y.2.2| - (C'_T / ν + 2)
      have hl1 : 1 ≤ l := by dsimp [l]; linarith
      have hl0 : 0 < l := lt_of_lt_of_le one_pos hl1
      have hw_le : (1 + |y.2.2|) ^ w ≤ A_reg ^ w * l ^ w := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ w
        have h1 : 3 + C'_T / ν ≤ (3 + C'_T / ν) * l :=
          le_mul_of_one_le_right (by positivity) hl1
        have heq : 1 + |y.2.2| = 3 + C'_T / ν + l := by dsimp [l]; ring
        unfold A_reg
        linarith
      have hy_le2 : y.1 ≤ 2 := by linarith
      have hz_tail : C'_T / ν + 2 + l ≤ |y.2.2| := by dsimp [l]; linarith
      have hp_tail :=
        (hTail 2 (by norm_num) ν hν hν_tail_le tr htr l hl0.le y.1 hy0 hy_le2 y.2 hz_tail).2.2.2
      rw [PartI.norm_ageJet_zero_zero] at hp_tail
      have hexp_sum :
          Real.exp (-(b_T * l / c)) + Real.exp (-(b_T * l ^ 2 / (C₀_T + ν * 2))) ≤
            2 * Real.exp (-(γ * l)) := by
        have h1 : γ * l ≤ b_T * l / c := by
          calc γ * l ≤ (b_T / c) * l := mul_le_mul_of_nonneg_right (min_le_left _ _) hl0.le
            _ = b_T * l / c := by ring
        have h2 : γ * l ≤ b_T * l ^ 2 / (C₀_T + ν * 2) := by
          have hsq : l ≤ l ^ 2 := by nlinarith
          calc γ * l ≤ (b_T / (C₀_T + ν * 2)) * l :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hl0.le
            _ = b_T * l / (C₀_T + ν * 2) := by ring
            _ ≤ b_T * l ^ 2 / (C₀_T + ν * 2) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hb_T.le) (by positivity)
        linarith [Real.exp_le_exp.2 (neg_le_neg h1), Real.exp_le_exp.2 (neg_le_neg h2)]
      have hexp_fac : l ^ w * Real.exp (-(γ * l)) ≤ K_fac := by
        have h1 := Real.pow_div_factorial_le_exp (γ * l) (by positivity) w
        have hfac : (0 : ℝ) < w.factorial := by exact_mod_cast w.factorial_pos
        have hγw : 0 < γ ^ w := pow_pos hγ w
        rw [div_le_iff₀ hfac, mul_pow] at h1
        have h2 : γ ^ w * (l ^ w * Real.exp (-(γ * l))) ≤ w.factorial := by
          calc γ ^ w * (l ^ w * Real.exp (-(γ * l)))
              = (γ ^ w * l ^ w) * Real.exp (-(γ * l)) := by ring
            _ ≤ (Real.exp (γ * l) * w.factorial) * Real.exp (-(γ * l)) :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
            _ = w.factorial * (Real.exp (γ * l) * Real.exp (-(γ * l))) := by ring
            _ = w.factorial := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        calc l ^ w * Real.exp (-(γ * l))
            = (γ ^ w)⁻¹ * (γ ^ w * (l ^ w * Real.exp (-(γ * l)))) := by field_simp [hγw.ne']
          _ ≤ (γ ^ w)⁻¹ * w.factorial := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hγw.le)
          _ = K_fac := by dsimp [K_fac]; ring
      have hp_le : |tr.p y.1 y.2| ≤ P2 * (2 * Real.exp (-(γ * l))) :=
        hp_tail.trans (mul_le_mul_of_nonneg_left hexp_sum hP2_nn)
      calc (1 + |y.2.2|) ^ w * |tr.p y.1 y.2|
          ≤ (A_reg ^ w * l ^ w) * (P2 * (2 * Real.exp (-(γ * l)))) :=
            mul_le_mul hw_le hp_le (abs_nonneg _) (by positivity)
        _ = 2 * A_reg ^ w * P2 * (l ^ w * Real.exp (-(γ * l))) := by ring
        _ ≤ 2 * A_reg ^ w * P2 * K_fac :=
            mul_le_mul_of_nonneg_left hexp_fac (by positivity)
        _ ≤ max (A_reg ^ w * C00) (2 * A_reg ^ w * P2 * K_fac) := le_max_right _ _
  intro m i
  exact wtdJetInterp Plane π2 hπ2 (fun x : ℝ × Plane => tr.p x.1 x.2) 1 hsm hUnw hW0 m i

/-- Pulls back a weighted Fréchet-jet bound on `(0, 1] × Plane` along `chartSwapLIE.symm` to an
`EarlyAll` bound on `trainProfile F`. -/
theorem pullback_earlyAll {F : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun y : ℝ × Plane => F y.1 y.2) (Ioi 0 ×ˢ univ))
    (hbd : ∀ w i : ℕ, ∃ C : ℝ, ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 →
      (1 + |y.2.2|) ^ w * ‖iteratedFDeriv ℝ i (fun z : ℝ × Plane => F z.1 z.2) y‖ ≤ C) :
    EarlyAll (trainProfile F) := by
  have heq : trainProfile F = (fun z : ℝ × Plane => F z.1 z.2) ∘ chartSwapLIE.symm := rfl
  have hsm : ContDiffOn ℝ ∞ (trainProfile F) ageDomain :=
    hf.comp chartSwapLIE.symm.contDiff.contDiffOn fun x hx => ⟨hx, trivial⟩
  intro m w
  choose C_i hC_i using fun i : ℕ => hbd w i
  set B : ℝ := ∑ i ∈ Finset.range (m + 1), max (C_i i) 0
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨hsm, B, hB0, fun x hx0 hx1 l hl => ?_⟩
  have hnorm : ‖iteratedFDeriv ℝ l (trainProfile F) x‖ =
      ‖iteratedFDeriv ℝ l (fun z : ℝ × Plane => F z.1 z.2) (x.2.2, (x.1, x.2.1))‖ := by
    rw [heq]
    exact chartSwapLIE.symm.norm_iteratedFDeriv_comp_right (fun z : ℝ × Plane => F z.1 z.2) x l
  rw [hnorm]
  have hpt : (1 + |x.2.1|) ^ w *
      ‖iteratedFDeriv ℝ l (fun z : ℝ × Plane => F z.1 z.2) (x.2.2, (x.1, x.2.1))‖ ≤
      max (C_i l) 0 :=
    (hC_i l (x.2.2, (x.1, x.2.1)) hx0 hx1).trans (le_max_left _ _)
  exact hpt.trans
    (Finset.single_le_sum (fun i _ => le_max_right (C_i i) 0)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hl)))

end UnforcedLeray.Short.IIb.EarlyJetAllAux

namespace UnforcedLeray.Short.IIb

open EarlyJetAllAux

/-- **All-order, fixed-threshold early-age (`0 < s ≤ 1`) chart-jet decay of `resChartProfile p`**
(`PartII-b:S2/1/2/1`, SP 439–467, 1294–1304, 2542–2548). -/
theorem resProfileEarlyJetAll_proof : UnforcedLeray.Short.IIb.ResProfileEarlyJetAll := by
  have hρ2 : (1 : ℝ) / 2 < 2 := by norm_num
  obtain ⟨ν_st, hν_st, hStream⟩ := trainStreamWtdBdd_fixed 2 hρ2
  obtain ⟨ν_pr, hν_pr, hPress⟩ := trainPressureWtdBdd_fixed
  refine ⟨min ν_st ν_pr, lt_min hν_st hν_pr, fun p htr hν hc hR _hP L N => ?_⟩
  have hν_st_le : p.ν ≤ ν_st := hν.le.trans (min_le_left _ _)
  have hν_pr_le : p.ν ≤ ν_pr := hν.le.trans (min_le_right _ _)
  have hc_tp : p.c = PartI.trainPeriod 2 p.ν := by
    rw [hc]
    unfold PartI.trainPeriod
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg p.ν_pos.le, Real.rpow_natCast]
  have hψ_sm : ContDiffOn ℝ ∞ (fun y : ℝ × Plane => p.train.ψ y.1 y.2) (Ioi 0 ×ˢ univ) :=
    PartI.trainStreamSmooth p.ν p.c p.ν_pos p.c_pos p.train htr
  have hp_sm : ContDiffOn ℝ ∞ (fun y : ℝ × Plane => p.train.p y.1 y.2) (Ioi 0 ×ˢ univ) :=
    p.train.isTrain.smooth_p.mono (prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hψ_all : EarlyAll (trainStream p) :=
    pullback_earlyAll hψ_sm fun w i => hStream p.ν p.c p.ν_pos hν_st_le hc_tp p.train htr w i 1
  have hp_bd : ∀ w i : ℕ, ∃ C : ℝ, ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 →
      (1 + |y.2.2|) ^ w * ‖iteratedFDeriv ℝ i (fun z : ℝ × Plane => p.train.p z.1 z.2) y‖ ≤ C := by
    have hgen : ∀ (c : ℝ) (tr : UnforcedLeray.B0140.TrainSol p.ν c),
        c = PartI.trainPeriod 2 p.ν → PartI.IsBUCTrain tr →
        ∀ w i : ℕ, ∃ C : ℝ, ∀ y : ℝ × Plane, 0 < y.1 → y.1 ≤ 1 →
          (1 + |y.2.2|) ^ w * ‖iteratedFDeriv ℝ i (fun z : ℝ × Plane => tr.p z.1 z.2) y‖ ≤ C := by
      rintro _ tr rfl htr'
      exact hPress p.ν p.ν_pos hν_pr_le tr htr'
    exact hgen p.c p.train hc_tp htr
  have hp_all : EarlyAll (trainPressure p) := pullback_earlyAll hp_sm hp_bd
  obtain ⟨hsm1, C1, _, hC1⟩ := earlyAll_coeffA1 p.ν hψ_all hp_all L N
  obtain ⟨hsm2, C2, _, hC2⟩ := earlyAll_coeffB1 p.ν hψ_all L N
  obtain ⟨hsm3, C3, _, hC3⟩ := earlyAll_coeffA2 p.ν hψ_all L N
  obtain ⟨hsm4, C4, _, hC4⟩ := earlyAll_coeffB2 p.ν hψ_all L N
  obtain ⟨hsm5, C5, _, hC5⟩ := earlyAll_coeffB3 p.ν hψ_all L N
  refine ⟨C1 + C2 + C3 + C4 + C5, fun m hm0 hm1 l hl => ?_⟩
  have hU : IsOpen {w : ℝ × (ℝ × ℝ) | 0 < w.1} := isOpen_lt continuous_const continuous_fst
  have hev : FarDecaySub.resChartProfile p =ᶠ[𝓝 m]
      fun w => resPolyMerid p.R p.ν (trainStream p) (trainPressure p) (chartSwap w) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hm0)
      (fun w hw => resChartProfile_eq_resPolyMerid p htr hw)
  have hnorm_eq : ‖iteratedFDeriv ℝ l (FarDecaySub.resChartProfile p) m‖ =
      ‖iteratedFDeriv ℝ l
        (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) (chartSwap m)‖ := by
    rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds,
      norm_iteratedFDeriv_comp_chartSwap
        (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) m l]
  rw [hnorm_eq]
  set x : ProfilePoint := chartSwap m
  have hx0 : 0 < x.2.2 := hm0
  have hx1 : x.2.2 ≤ 1 := hm1
  have hpoly := norm_iteratedFDeriv_resPolyMerid_le hR hx0 hsm1 hsm2 hsm3 hsm4 hsm5 l
  have hW_pos : 0 ≤ (1 + |x.2.1|) ^ N := by positivity
  have hb1 := hC1 x hx0 hx1 l hl
  have hb2 := hC2 x hx0 hx1 l hl
  have hb3 := hC3 x hx0 hx1 l hl
  have hb4 := hC4 x hx0 hx1 l hl
  have hb5 := hC5 x hx0 hx1 l hl
  change (1 + |x.2.1|) ^ N *
      ‖iteratedFDeriv ℝ l (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) x‖ ≤
    C1 + C2 + C3 + C4 + C5
  calc (1 + |x.2.1|) ^ N *
        ‖iteratedFDeriv ℝ l (resPolyMerid p.R p.ν (trainStream p) (trainPressure p)) x‖
      ≤ (1 + |x.2.1|) ^ N *
          (‖iteratedFDeriv ℝ l (coeffA₁ p.ν (trainStream p) (trainPressure p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₁ p.ν (trainStream p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffA₂ p.ν (trainStream p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₂ p.ν (trainStream p)) x‖ +
            ‖iteratedFDeriv ℝ l (coeffB₃ p.ν (trainStream p)) x‖) :=
        mul_le_mul_of_nonneg_left hpoly hW_pos
    _ ≤ C1 + C2 + C3 + C4 + C5 := by linarith

end UnforcedLeray.Short.IIb
