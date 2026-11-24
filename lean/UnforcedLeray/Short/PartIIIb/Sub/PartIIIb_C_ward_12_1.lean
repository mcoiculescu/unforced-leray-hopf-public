import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Defs
import UnforcedLeray.Short.PartI.StatementsTrain

/-!
# Decomposition of `bgTrainStreamYoungJets_of` (source 439-459, 5461-5464)

Source of record: `the November 2 reference manuscript` (73 pages).

`Ψ = ψ` splits as `ψ̃ + S∘η` (`S = meanStream`, `ψ̃ = ψ - S`).  The fluctuation `ψ̃` is bounded
in the weighted age-jet norm by `TrainFluctuationDecay` (`sct:fluctuation`, 439-446), the mean
`S` by `TrainMeanExpansion` (`sct:expansion`, 447-459, `p = ⊤`); the age-jets are converted into
the full iterated Fréchet derivative on `ℝ × ℝ²` by a calculus lemma.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI (ageJet meanStream)

/-- **Weighted age-jets of the fluctuation `ψ̃ = ψ - S`** (source 439-446, `ρ = 2`, `m = 3`; the
period of `p.train` is `p.c = (p.ν²)⁻¹ = trainPeriod 2 p.ν`): with `ν ≤ ν₀`, some `M` (depending on
`p`) bounds `(1+|η|)³ ‖∂_s^ℓ D^j ψ̃(s,z)‖` for `ℓ + j ≤ 3`, all `s > 0`, `z`. -/
def BgFluctWeighted : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ M : ℝ, ∀ ℓ j : ℕ, ℓ + j ≤ 3 → ∀ s : ℝ, 0 < s → ∀ z : Plane,
        (1 + |z.2|) ^ 3 *
          ‖ageJet ℓ j (fun r z => p.train.ψ r z - meanStream p.train r z.2) s z‖ ≤ M

/-- **Weighted derivatives of the mean stream** (source 447-459 with `p = ⊤`, `N = 0`,
`m ≤ 3`; `(1+|η|)³ ≤ 4(1+|η|³)`; `(1+s)^{(m-b-1)/2-ℓ} ≤ (1+1/ν)³`): with `ν ≤ ν₀`, some `M`
bounds `(1+|η|)³ |∂_η^b ∂_s^ℓ S(s,η)|` for `b + ℓ ≤ 3`, `0 < s ≤ 1/ν`, all `η` (strictly positive `s`: `iteratedDeriv` in the age variable at `s = 0` reads the
profile at `r < 0`, where the train is not constrained; the consumer needs only `s > 0`). -/
def BgMeanWeighted : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ M : ℝ, ∀ b ℓ : ℕ, b + ℓ ≤ 3 → ∀ s : ℝ, 0 < s → s ≤ p.ν⁻¹ → ∀ η : ℝ,
        (1 + |η|) ^ 3 *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => meanStream p.train r e) s) η| ≤ M

/-- **The mean stream is jointly smooth for `s > 0`** (source 397 `sct:mean`: "`S` smooth for
`s > 0`"; `S = c⁻¹∫ψ dq` with `ψ` jointly smooth on `s > 0` and all derivatives bounded on
`[s₁,s₂] × ℝ²`, `IsBUCTrain`; differentiation under the integral; or from
`PartI.TrainMeanEquations` if it is available). -/
def BgMeanSmooth : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStream p.train x.1 x.2) (Ioi 0 ×ˢ univ)

/-- **Age-jets control the full derivative** (pure calculus): for `F` jointly `C^∞` on
`{s > 0}`, the `l`-th Fréchet derivative of `(s,z) ↦ F s z` on `ℝ × ℝ²` is bounded by a constant
(depending only on `l`) times the sum of the norms of the mixed jets `∂_s^ℓ D^{l-ℓ}F`
(split each argument `v = (v.1,0) + (0,v.2)`, multilinearity, symmetry of the `C^l` derivative,
and `∂_s`, `D_z` commute). -/
def MixedToFull : Prop :=
  ∀ l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ F : ℝ → Plane → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ x : ℝ × Plane, 0 < x.1 →
      ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => F x.1 x.2) x‖ ≤
        C * ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ) F x.1 x.2‖

/-- **Jets of a function of `η` alone** (norm of the `j`-th Fréchet derivative of `h ∘ snd` is at
most `|h^{(j)}|`; here `h = ∂_s^ℓ g(s,·)`): for `g` jointly `C^∞` on `{s > 0}`,
`‖∂_s^ℓ D^j (g(s, z.2))‖ ≤ |∂_η^j ∂_s^ℓ g(s, z.2)|`. -/
def MeanSliceJet : Prop :=
  ∀ g : ℝ → ℝ → ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => g x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (ℓ j : ℕ) (s : ℝ), 0 < s → ∀ z : Plane,
      ‖ageJet ℓ j (fun r z => g r z.2) s z‖ ≤
        |iteratedDeriv j (fun e => iteratedDeriv ℓ (fun r => g r e) s) z.2|

theorem bgTrainStreamYoungJets_of_parts (hF : BgFluctWeighted) (hM : BgMeanWeighted)
    (hS : BgMeanSmooth) (hC : MixedToFull) (hJ : MeanSliceJet) : BgTrainStreamYoungJets := by
  intro dm dp hdm
  obtain ⟨ν₁, hν₁, hF'⟩ := hF dm dp hdm
  obtain ⟨ν₂, hν₂, hM'⟩ := hM dm dp hdm
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, ?_⟩
  intro p d hreg hν
  obtain ⟨M₁, hM₁⟩ := hF' p d hreg (hν.trans (min_le_left _ _))
  obtain ⟨M₂, hM₂⟩ := hM' p d hreg (hν.trans (min_le_right _ _))
  choose C hC0 hC1 using hC
  have hSm := hS p d dm dp hreg
  have hΨ := hreg.train_stream_smooth
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hGs : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => meanStream p.train x.1 x.2.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    hSm.comp (f := fun x : ℝ × Plane => (x.1, x.2.2))
      ((contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn)
      (fun x hx => ⟨hx.1, trivial⟩)
  have hΨt : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => p.train.ψ x.1 x.2 - meanStream p.train x.1 x.2.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := hΨ.sub hGs
  refine ⟨∑ l ∈ Finset.range 4, C l * ((l + 1 : ℝ) * (|M₁| + |M₂|)), ?_⟩
  intro l hl x hx0 hx1
  have hlx : l ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hxU : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hx0, trivial⟩
  have hca1 : ContDiffAt ℝ l (fun x : ℝ × Plane => p.train.ψ x.1 x.2 -
      meanStream p.train x.1 x.2.2) x :=
    ((hΨt.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast le_top))
  have hca2 : ContDiffAt ℝ l (fun x : ℝ × Plane => meanStream p.train x.1 x.2.2) x :=
    ((hGs.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast le_top))
  have hsplit : (fun x : ℝ × Plane => p.train.ψ x.1 x.2) =
      (fun x : ℝ × Plane => p.train.ψ x.1 x.2 - meanStream p.train x.1 x.2.2) +
        (fun x : ℝ × Plane => meanStream p.train x.1 x.2.2) := by
    funext y; simp
  rw [hsplit, iteratedFDeriv_add_apply hca1 hca2]
  have hw : 0 ≤ (1 + |x.2.2|) ^ 3 := by positivity
  have hA := hC1 l (fun r z => p.train.ψ r z - meanStream p.train r z.2) hΨt x hx0
  have hB := hC1 l (fun r z => meanStream p.train r z.2) hGs x hx0
  have hsum1 : (1 + |x.2.2|) ^ 3 *
      ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ)
        (fun r z => p.train.ψ r z - meanStream p.train r z.2) x.1 x.2‖ ≤
      (l + 1 : ℝ) * |M₁| := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ ℓ ∈ Finset.range (l + 1), |M₁| := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have := hM₁ ℓ (l - ℓ) (by have := Finset.mem_range.mp hℓ; omega) x.1 hx0 x.2
          exact this.trans (le_abs_self _)
      _ = (l + 1 : ℝ) * |M₁| := by simp
  have hsum2 : (1 + |x.2.2|) ^ 3 *
      ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ)
        (fun r z => meanStream p.train r z.2) x.1 x.2‖ ≤ (l + 1 : ℝ) * |M₂| := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ ℓ ∈ Finset.range (l + 1), |M₂| := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have hℓ' := Finset.mem_range.mp hℓ
          have h1 := hJ (fun r e => meanStream p.train r e) hSm ℓ (l - ℓ) x.1 hx0 x.2
          have h2 := hM₂ (l - ℓ) ℓ (by omega) x.1 hx0 hx1 x.2.2
          calc _ ≤ (1 + |x.2.2|) ^ 3 *
                |iteratedDeriv (l - ℓ)
                  (fun e => iteratedDeriv ℓ (fun r => meanStream p.train r e) x.1) x.2.2| :=
                mul_le_mul_of_nonneg_left h1 hw
            _ ≤ |M₂| := h2.trans (le_abs_self _)
      _ = (l + 1 : ℝ) * |M₂| := by simp
  have hCl := hC0 l
  have hle : C l * ((l + 1 : ℝ) * (|M₁| + |M₂|)) ≤
      ∑ l ∈ Finset.range 4, C l * ((l + 1 : ℝ) * (|M₁| + |M₂|)) :=
    Finset.single_le_sum (f := fun l => C l * ((l + 1 : ℝ) * (|M₁| + |M₂|)))
      (fun i _ => mul_nonneg (hC0 i) (by positivity)) hlx
  refine le_trans ?_ hle
  calc (1 + |x.2.2|) ^ 3 * ‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => p.train.ψ x.1 x.2 -
        meanStream p.train x.1 x.2.2) x + iteratedFDeriv ℝ l
          (fun x : ℝ × Plane => meanStream p.train x.1 x.2.2) x‖
      ≤ (1 + |x.2.2|) ^ 3 * (‖iteratedFDeriv ℝ l (fun x : ℝ × Plane => p.train.ψ x.1 x.2 -
        meanStream p.train x.1 x.2.2) x‖ + ‖iteratedFDeriv ℝ l
          (fun x : ℝ × Plane => meanStream p.train x.1 x.2.2) x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ ≤ (1 + |x.2.2|) ^ 3 * (C l * ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ)
          (fun r z => p.train.ψ r z - meanStream p.train r z.2) x.1 x.2‖ +
        C l * ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ)
          (fun r z => meanStream p.train r z.2) x.1 x.2‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hw
    _ = C l * ((1 + |x.2.2|) ^ 3 * ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ)
          (fun r z => p.train.ψ r z - meanStream p.train r z.2) x.1 x.2‖) +
        C l * ((1 + |x.2.2|) ^ 3 * ∑ ℓ ∈ Finset.range (l + 1), ‖ageJet ℓ (l - ℓ)
          (fun r z => meanStream p.train r z.2) x.1 x.2‖) := by ring
    _ ≤ C l * ((l + 1 : ℝ) * |M₁|) + C l * ((l + 1 : ℝ) * |M₂|) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum1 hCl) (mul_le_mul_of_nonneg_left hsum2 hCl)
    _ = C l * ((l + 1 : ℝ) * (|M₁| + |M₂|)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
