import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, task `PartII-a:R02/6`: the mean-stress profile bounds (decomposition, conditional)

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`,
`g = \overline{v₁ v₂}`), 439-446 (`sct:fluctuation`) and 1259-1276 (late residual table).

Target: `LateMeanStress` (`Sub/R02.lean`): `(1+η²/s)^m |K^ℓ ∂_η^a g| ≤ P e^{-κνs/c²}` for `s ≥ 1`,
`g = trainProfile of meanStress`.



1. `g(s, η) = hmean c (ṽ₁ ṽ₂)(η)` with `ṽ = hfluct c v` (because `\bar v₂ = 0` by `sct:mean`):
   `hmean_mul_eq_hfluct_mul` (leaf `HmeanMulFluct`).
2. `∂_η^a ∂_s^k` commutes with the cell average (differentiation under the integral over the
   compact `q`-interval): leaf `HmeanMixedDeriv`.  Together with 1: `MeanStressDerivForm`.
3. The integrand `∂_η^{a} ∂_s^k (ṽ₁ṽ₂)(q, ·)` is expanded by the Leibniz rule (leaf `MixedLeibniz`)
   and each factor is bounded by `TrainFluctuationDecay` (leaf `FluctVelSliceBound`), giving
   `MeanStressIntegrandBound` (leaf, assembled from the two with `finite_uniform` and `ExpPowAbsorb`).
4. The average of a function bounded uniformly in `q` is bounded by the same constant
   (`avg_bound`, proved here), so the term `(1+η²/s)^m |η|^i s^k |∂_η^{i+a} ∂_s^k g|` has the
   exponential bound; `late_assembly` (`Sub/R02_2.lean`) then gives `K^ℓ ∂_η^a g`.

`lateMeanStress_of_sub` is the conditional theorem; the unconditional statement
`lateMeanStress_of (hF) (hE) (hS) : LateMeanStress` is the task file
`Short/PartII-a/Tasks/R02/MeanStress.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0184 UnforcedLeray.B0190
open UnforcedLeray.Short.PartI (meanStress hmean hfluct)

/-- The product `ṽ₁ ṽ₂` of the fluctuations (`hfluct`) of the two velocity components of the
train at age `r`, as a function of `z = (q, η)`; `meanStress = hmean (ṽ₁ṽ₂)` by `sct:mean`. -/
def fluctProd {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (r : ℝ) (z : ℝ × ℝ) : ℝ :=
  UnforcedLeray.Short.PartI.hfluct c (fun w => tr.v r w 0) z *
    UnforcedLeray.Short.PartI.hfluct c (fun w => tr.v r w 1) z

/-! ### Leaves -/

/-- **Cell algebra** (source lines 397-404): if `\bar g(η) = 0` then
`\overline{f g}(η) = \overline{\tilde f \tilde g}(η)` for continuous `f, g` on the cylinder
(`fg = (f̃+\bar f)(g̃+\bar g)`; the cross terms `\bar f \overline{\tilde g}` and
`\bar g \overline{\tilde f}` vanish because `\overline{\tilde h} = 0`, and `\bar f \bar g = 0`). -/
def HmeanMulFluct : Prop :=
  ∀ (c η : ℝ), 0 < c → ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g → hmean c g η = 0 →
    hmean c (fun z => f z * g z) η = hmean c (fun z => hfluct c f z * hfluct c g z) η

/-- **Smoothness of the mean stress and of the fluctuation products** (source lines 397-404):
`g(s, η) = \overline{v₁v₂}`, the fluctuations `ṽ_j(s, (q, η)) = hfluct c (v_j)` and their product
`ṽ₁ṽ₂` are `C^∞` for `s > 0` (`B0140.IsTrain.smooth_v` gives `v` smooth; `HmeanContDiff`, proved as
`hmeanContDiff` in `Short/PartI/Tasks/TrainMeanEquations/HmeanContDiff.lean`, gives smoothness of
`hmean`). -/
def MeanStressSmooth : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanStress tr x.1 x.2) (Ioi 0 ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => fluctProd tr x.1 x.2) (Ioi 0 ×ˢ univ) ∧
    ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => hfluct c (fun w => tr.v x.1 w j) x.2)
      (Ioi 0 ×ˢ univ)

/-- **The age derivative commutes with the cell average, iterated** (from `HmeanDerivS`,
`PartI/Sub/T01.lean`, proved as `hmeanDerivS`): for `f` jointly `C^∞` on `(0,∞) × ℝ²` and `s > 0`,
`∂_s^k \bar f(s, η) = \overline{∂_s^k f}(s, η)`.  (Induction on `k`, applying `HmeanDerivS` to
the jointly smooth `∂_s^k f` -- `AgeDerivSmooth` -- and using that the identity holds for all
`r > 0` near `s`.) -/
def HmeanAgeIter : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ → ℝ × ℝ → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (k : ℕ) (s : ℝ), 0 < s → ∀ η : ℝ,
      iteratedDeriv k (fun r => hmean c (f r) η) s =
        hmean c (fun z => iteratedDeriv k (fun r => f r z) s) η

/-- **The `η`-derivative commutes with the cell average** (differentiation under the integral over
the compact interval `(-c/2, c/2]`, `Kernels.iteratedFDeriv_integral_eq` in
`Lib/Kernels/ParamIntegral.lean` with `μ = volume.restrict (Ioc (-c/2) (c/2))`, `U = univ`,
`F q η = h (q, η)`): for `h` globally `C^∞` on the plane,
`∂_η^a \bar h(η) = \overline{∂_η^a h}(η)`. -/
def HmeanEtaDeriv : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h : ℝ × ℝ → ℝ, ContDiff ℝ ∞ h → ∀ (a : ℕ) (η : ℝ),
    iteratedDeriv a (fun e => hmean c h e) η =
      hmean c (fun z => iteratedDeriv a (fun e => h (z.1, e)) z.2) η

/-- **Mixed derivatives commute with the cell average** (differentiation under the integral over
the compact interval `(-c/2, c/2]`; `Lib/Kernels/ParamIntegral.lean`,
`iteratedFDeriv_integral_eq`): for `f` jointly `C^∞` on `(0,∞) × ℝ²`, `s > 0`,
`∂_η^a ∂_s^k \bar f = \overline{∂_η^a ∂_s^k f}`.  (From `HmeanAgeIter` for the age derivative,
then `HmeanEtaDeriv` for the smooth plane function `z ↦ ∂_s^k f(s, z)`.) -/
def HmeanMixedDeriv : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ → ℝ × ℝ → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => f x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (a k : ℕ) (s η : ℝ), 0 < s →
      iteratedDeriv a (fun e => iteratedDeriv k (fun r => hmean c (f r) e) s) η =
        hmean c (fun z => iteratedDeriv a
          (fun e => iteratedDeriv k (fun r => f r (z.1, e)) s) z.2) η

/-- **Leibniz rule for the mixed derivative of a product** (calculus; Mathlib
`iteratedDeriv_mul` twice, first in the age variable, then in `η`): for `A, B` jointly `C^∞` on
`(0,∞) × ℝ` and `s > 0`,
`∂_η^a ∂_s^k (A B) = ∑_{i≤a} ∑_{l≤k} C(a,i) C(k,l) (∂_η^i ∂_s^l A)(∂_η^{a-i} ∂_s^{k-l} B)`. -/
def MixedLeibniz : Prop :=
  ∀ A B : ℝ → ℝ → ℝ,
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => A x.1 x.2) (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => B x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ (a k : ℕ) (s η : ℝ), 0 < s →
      iteratedDeriv a (fun e => iteratedDeriv k (fun r => A r e * B r e) s) η =
        ∑ i ∈ Finset.range (a + 1), ∑ l ∈ Finset.range (k + 1),
          (a.choose i : ℝ) * (k.choose l : ℝ) *
            (iteratedDeriv i (fun e => iteratedDeriv l (fun r => A r e) s) η *
              iteratedDeriv (a - i) (fun e => iteratedDeriv (k - l) (fun r => B r e) s) η)

/-- **Slice bound for the velocity fluctuation** (`sct:fluctuation`, source lines 439-446; the
second block of `TrainFluctuationDecay`): for fixed `m', i, l` there are a polynomial majorant and
`κ > 0` with
`(1+η²)^{m'} |∂_η^i ∂_s^l (\tilde v_j)(s, (q, η))| ≤ P e^{-κνs/c²}` for all `q, η`, `s > 0`,
`j = 0, 1` (`\tilde v_j = hfluct c (v_j)`).  (From `wSupNorm (2m')` of
`ageJet l i (fun r => hfluct c (tr.v r)) s`, since `sqrt (jap (2m') z) = (1+η²)^{m'}`; the
component `j` of a vector is bounded by its norm, and the `η`-derivative of the slice is bounded by
the operator norm of the jet.) -/
def FluctVelSliceBound : Prop :=
  ∀ (ρ : ℝ) (m' i l : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ (j : Fin 2) (q η s : ℝ), 0 < s →
        (1 + η ^ 2) ^ m' * |iteratedDeriv i (fun e => iteratedDeriv l
            (fun r => hfluct (ν ^ (-ρ)) (fun w => tr.v r w j) (q, e)) s) η| ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2))

/-- **Integrand bound** (Leibniz + `FluctVelSliceBound` + absorption of `s^k`): the weighted
`η`-derivatives of the fluctuation product `ṽ₁ṽ₂` are exponentially small, uniformly in `q`:
`(1+η²/s)^m |η|^i s^k |∂_η^{i+a} ∂_s^k (ṽ₁ṽ₂)(q, ·)| ≤ P e^{-κνs/c²}` for `s ≥ 1`.
(Each Leibniz term is a product of two slice bounds with `m' = 2(m+i)`, whose product is
`≤ P² e^{-2κ'νs/c²} (1+η²)^{-2(m+i)}`; the weight satisfies
`(1+η²/s)^m |η|^i ≤ (1+η²)^{m+i}` for `s ≥ 1`; the finite sum is uniformized by
`finite_uniform` and `s^k` is absorbed by `ExpPowAbsorb`.) -/
def MeanStressIntegrandBound : Prop :=
  ∀ (ρ : ℝ) (m a i k : ℕ), 1 / 2 < ρ → ∃ (C : ℝ) (N : ℕ) (κ ν₀ : ℝ), 0 < κ ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ q η s : ℝ, 1 ≤ s →
        (1 + η ^ 2 / s) ^ m * (|η| ^ i * s ^ k *
          |iteratedDeriv (i + a) (fun e => iteratedDeriv k
            (fun r => fluctProd tr r (q, e)) s) η|) ≤
          polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * s / (ν ^ (-ρ)) ^ 2))

/-- **The derivative form of the mean stress** (source lines 397-404; from `HmeanMulFluct`,
`HmeanMixedDeriv`, `TrainMeanEquations`' third conjunct `\bar v₂ = 0`): for `s > 0`,
`∂_η^a ∂_s^k g(s, η) = \overline{∂_η^a ∂_s^k (ṽ₁ṽ₂)}(η)`.  (For all `r > 0`, `e`:
`g(r, e) = hmean c (ṽ₁ṽ₂(r))(e)`, so the age derivatives at `s > 0` agree; then apply
`HmeanMixedDeriv` to `f r z = ṽ₁ṽ₂(r, z)`, smooth by `MeanStressSmooth`.) -/
def MeanStressDerivForm : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ (a k : ℕ) (s η : ℝ),
    0 < s →
      iteratedDeriv a (fun e => iteratedDeriv k (fun r => meanStress tr r e) s) η =
        hmean c (fun z => iteratedDeriv a
          (fun e => iteratedDeriv k (fun r => fluctProd tr r (z.1, e)) s) z.2) η

/-! ### The average of a bounded function (proved) -/

theorem avg_bound {c η V B : ℝ} (hc : 0 < c) (hV : 0 ≤ V) (h : ℝ → ℝ → ℝ)
    (hb : ∀ q ∈ Ioc (-c / 2) (c / 2), V * |h q η| ≤ B) :
    V * |hmean c (fun z : ℝ × ℝ => h z.1 z.2) η| ≤ B := by
  have hB0 : 0 ≤ B := by
    have h0 : (0 : ℝ) ∈ Ioc (-c / 2) (c / 2) := ⟨by linarith, by linarith⟩
    exact (mul_nonneg hV (abs_nonneg _)).trans (hb 0 h0)
  have h1 : ‖∫ q in Ioc (-c / 2) (c / 2), V * h q η‖ ≤ B * c := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-c / 2) (c / 2))
      (f := fun q => V * h q η) (C := B) measure_Ioc_lt_top
      (fun q hq => by
        have := hb q hq
        rwa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hV])
    rwa [Real.volume_real_Ioc_of_le (by linarith), show c / 2 - (-c / 2) = c by ring] at this
  have e1 : hmean c (fun z : ℝ × ℝ => h z.1 z.2) η = c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2), h q η := rfl
  rw [e1]
  calc V * |c⁻¹ * ∫ q in Ioc (-c / 2) (c / 2), h q η|
      = c⁻¹ * ‖∫ q in Ioc (-c / 2) (c / 2), V * h q η‖ := by
        rw [integral_const_mul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hV,
          abs_of_pos (inv_pos.2 hc)]
        ring
    _ ≤ c⁻¹ * (B * c) := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hc).le
    _ = B := by field_simp

/-! ### The conditional theorem -/

/-- **`PartII-a:R02/6`, conditional** (`LateMeanStress`). -/
theorem lateMeanStress_of_sub (hK : KExpansion) (hC : ProfileIterComm) (hD : ProfileDict)
    (hSm : MeanStressSmooth) (hDF : MeanStressDerivForm) (hIB : MeanStressIntegrandBound) :
    LateMeanStress := by
  intro ρ m a ℓ hρ
  let ι : Type := Σ ν : ℝ, {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)) // UnforcedLeray.Short.PartI.IsBUCTrain tr} × ProfilePoint
  have key := late_assembly (ι := ι) hK hC
    (fun j => 0 < j.1 ∧ 1 ≤ j.2.2.2.2) (fun j => j.1) (fun j => j.1 ^ (-ρ))
    (fun j => j.2.2)
    (fun j => trainProfile fun s z => meanStress j.2.1.1 s z.2)
    (fun κ j => Real.exp (-(κ * j.1 * j.2.2.2.2 / (j.1 ^ (-ρ)) ^ 2)))
    (fun κ j _ => (Real.exp_pos _).le)
    (by
      intro κ κ' j hj hκ' hκκ'
      apply Real.exp_le_exp.2
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have : 0 ≤ j.1 * j.2.2.2.2 := mul_nonneg hj.1.le (by linarith [hj.2])
      nlinarith)
    (fun j hj => ⟨hj.1, Real.rpow_pos_of_pos hj.1 _, hj.2⟩)
    (by
      rintro ⟨ν, ⟨tr, hb⟩, x⟩ ⟨hν, _⟩
      exact contDiffOn_trainProfile_of_eta
        (hSm ν (ν ^ (-ρ)) hν (Real.rpow_pos_of_pos hν _) tr hb).1)
    ℓ a 0 m
    (by
      intro i k
      obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := hIB ρ m a i k hρ
      refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
      rintro ⟨ν, ⟨tr, hb⟩, x⟩ ⟨hν, hx⟩ hνν₀
      have hs0 : 0 < x.2.2 := by linarith
      have hc : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν _
      have hFs := contDiffOn_trainProfile_of_eta (hSm ν (ν ^ (-ρ)) hν hc tr hb).1
      have hdict := hD _ hFs (i + a) 0 k x hs0
      simp only [iteratedDeriv_zero] at hdict
      show (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
          |(partialEta^[i + a] (partialQ^[0] (partialAge^[k]
            (trainProfile fun s z => meanStress tr s z.2)))) x|) ≤
        polyConst C N ν (ν ^ (-ρ)) * Real.exp (-(κ * ν * x.2.2 / (ν ^ (-ρ)) ^ 2))
      rw [hdict, hDF ν (ν ^ (-ρ)) hν hc tr hb (i + a) k x.2.2 x.2.1 hs0]
      have hV : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k) := by positivity
      have := avg_bound (c := ν ^ (-ρ)) (η := x.2.1) hc hV
        (fun q η' => iteratedDeriv (i + a) (fun e => iteratedDeriv k
          (fun r => fluctProd tr r (q, e)) x.2.2) η')
        (fun q _ => by
          have := H ν hν hνν₀ tr hb q x.2.1 x.2.2 hx
          calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k) *
                |iteratedDeriv (i + a) (fun e => iteratedDeriv k
                  (fun r => fluctProd tr r (q, e)) x.2.2) x.2.1|
              = (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
                |iteratedDeriv (i + a) (fun e => iteratedDeriv k
                  (fun r => fluctProd tr r (q, e)) x.2.2) x.2.1|) := by ring
            _ ≤ _ := this)
      calc (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k *
            |hmean (ν ^ (-ρ)) (fun z : ℝ × ℝ => iteratedDeriv (i + a) (fun e => iteratedDeriv k
              (fun r => fluctProd tr r (z.1, e)) x.2.2) z.2) x.2.1|)
          = (1 + x.2.1 ^ 2 / x.2.2) ^ m * (|x.2.1| ^ i * x.2.2 ^ k) *
            |hmean (ν ^ (-ρ)) (fun z : ℝ × ℝ => iteratedDeriv (i + a) (fun e => iteratedDeriv k
              (fun r => fluctProd tr r (z.1, e)) x.2.2) z.2) x.2.1| := by ring
        _ ≤ _ := this)
  obtain ⟨C, N, κ, ν₀, hκ, hν₀, H⟩ := key
  refine ⟨C, N, κ, ν₀, hκ, hν₀, ?_⟩
  intro ν hν hνν₀ tr hb x hx
  exact H ⟨ν, ⟨tr, hb⟩, x⟩ ⟨hν, hx⟩ hνν₀

end UnforcedLeray.Short.PartIIa
