import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_1_1_1_1.Tail.Elliptic
import UnforcedLeray.Short.PartI.Sub.PartI_TrainHeatFixed

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace UnforcedLeray.Short.IIb.WeightedTrainFluctAux

open UnforcedLeray
open UnforcedLeray.Short.PartI
open UnforcedLeray.Cyl (Plane)

/-- **Source leaf (SP 460-467 with 481-509, fixed parameters 427-435)**: the transverse tail of the
stream fluctuation `ψ̃ = ψ - \bar ψ` (the nonzero modes by the stream kernel `e^{-|k||η|}/(2|k|)`, the
zero mode by its two decaying primitives, 503-509), at fixed parameters: for `ρ > 1/2` one `ν₀`; for
every BUC train with `ν ≤ ν₀` and all `ℓ, j` there are constants (depending on the train) with
`‖∂_s^ℓ D^j ψ̃(s, z)‖ ≤ C(1+S)^N {e^{-b l} + e^{-b l²/(C₀+νS)}}` for `0 < s ≤ S`, `l ≥ 0`,
`|η| ≥ C'/ν + 2 + l`. -/
def FluctTransverseTailFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ ℓ j : ℕ,
      ∃ b C₀ C' C : ℝ, ∃ N : ℕ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧
        ∀ S_ : ℝ, 0 ≤ S_ → ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane,
          C' / ν + 2 + l ≤ |z.2| →
            ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ ≤
              C * (1 + S_) ^ N *
                (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))

private theorem pow_mul_exp_neg_le (k : ℕ) {β x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(β * x)) ≤ k.factorial / β ^ k := by
  have h := Real.pow_div_factorial_le_exp (β * x) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  have hβk : (0 : ℝ) < β ^ k := by positivity
  rw [le_div_iff₀ hβk]
  have he : 0 < Real.exp (β * x) := Real.exp_pos _
  have e1 : Real.exp (-(β * x)) * Real.exp (β * x) = 1 := by
    rw [← Real.exp_add]; simp
  calc x ^ k * Real.exp (-(β * x)) * β ^ k
      = (β ^ k * x ^ k) * Real.exp (-(β * x)) := by ring
    _ ≤ (Real.exp (β * x) * k.factorial) * Real.exp (-(β * x)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = k.factorial := by
        calc (Real.exp (β * x) * k.factorial) * Real.exp (-(β * x))
            = (Real.exp (-(β * x)) * Real.exp (β * x)) * k.factorial := by ring
          _ = k.factorial := by rw [e1, one_mul]

/-- The weighted core: `(1+l)^m e^{-b l} ≤ e^b m!/b^m`. -/
private theorem core1 (m : ℕ) {b l : ℝ} (hb : 0 < b) (hl : 0 ≤ l) :
    (1 + l) ^ m * Real.exp (-(b * l)) ≤ Real.exp b * (m.factorial / b ^ m) := by
  have h := pow_mul_exp_neg_le m hb (by linarith : 0 ≤ 1 + l)
  have : Real.exp (-(b * l)) = Real.exp b * Real.exp (-(b * (1 + l))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  calc (1 + l) ^ m * (Real.exp b * Real.exp (-(b * (1 + l))))
      = Real.exp b * ((1 + l) ^ m * Real.exp (-(b * (1 + l)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The Gaussian core: `(1+l)^m e^{-b l²/D} ≤ e^{b/C₀} m! (2D/b)^m` for `D ≥ C₀ > 0`. -/
private theorem core2 (m : ℕ) {b C₀ D l : ℝ} (hb : 0 < b) (hC₀ : 0 < C₀) (hD : C₀ ≤ D)
    (hl : 0 ≤ l) :
    (1 + l) ^ m * Real.exp (-(b * l ^ 2 / D)) ≤
      Real.exp (b / C₀) * (m.factorial * (2 * D / b) ^ m) := by
  have hD0 : 0 < D := lt_of_lt_of_le hC₀ hD
  set x := 1 + l with hx
  have hx1 : 1 ≤ x := by linarith
  have hl2 : x ^ 2 ≤ 2 + 2 * l ^ 2 := by nlinarith [sq_nonneg (l - 1)]
  have hβ : 0 < b / (2 * D) := by positivity
  have h := pow_mul_exp_neg_le m hβ (by positivity : 0 ≤ x ^ 2)
  have e1 : Real.exp (-(b * l ^ 2 / D)) ≤
      Real.exp (b / C₀) * Real.exp (-(b / (2 * D) * x ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : b / D ≤ b / C₀ := div_le_div_of_nonneg_left hb.le hC₀ hD
    have h2 : b / (2 * D) * x ^ 2 ≤ b / (2 * D) * (2 + 2 * l ^ 2) :=
      mul_le_mul_of_nonneg_left hl2 hβ.le
    have h3 : b / (2 * D) * (2 + 2 * l ^ 2) = b / D + b * l ^ 2 / D := by
      field_simp
    linarith
  have hxm : x ^ m ≤ (x ^ 2) ^ m := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hx1 (by omega)
  have hpos : 0 ≤ Real.exp (-(b * l ^ 2 / D)) := (Real.exp_pos _).le
  calc x ^ m * Real.exp (-(b * l ^ 2 / D))
      ≤ x ^ m * (Real.exp (b / C₀) * Real.exp (-(b / (2 * D) * x ^ 2))) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
    _ ≤ (x ^ 2) ^ m * (Real.exp (b / C₀) * Real.exp (-(b / (2 * D) * x ^ 2))) :=
        mul_le_mul_of_nonneg_right hxm (by positivity)
    _ = Real.exp (b / C₀) * ((x ^ 2) ^ m * Real.exp (-(b / (2 * D) * x ^ 2))) := by ring
    _ ≤ Real.exp (b / C₀) * (m.factorial / (b / (2 * D)) ^ m) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
        congr 1
        rw [div_eq_mul_inv, ← inv_pow, inv_div]

set_option maxHeartbeats 800000 in
theorem fluctDoubledWeightPoly_of_transverseTail (h1 : TrainFluctAgeJetFixed)
    (h2 : FluctTransverseTailFixed) : UnforcedLeray.Short.PartIIIb.Concrete.FluctDoubledWeightPoly := by
  suffices hW : ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ,
        ∀ s : ℝ, 0 < s → ∀ z : Plane,
          (1 + |z.2|) ^ m *
              ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ ≤
            C * (1 + s) ^ N from
    fun ρ hρ => let ⟨ν₀, hν₀, H⟩ := hW ρ hρ; ⟨ν₀, hν₀, fun ν hν hle tr htr m ℓ j => H ν hν hle tr htr (2 * m) ℓ j⟩
  intro ρ hρ
  obtain ⟨ν1, hν1, H1⟩ := h1 ρ hρ
  obtain ⟨ν2, hν2, H2⟩ := h2 ρ hρ
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun ν hν hle tr htr m ℓ j => ?_⟩
  obtain ⟨K, κ, hκ, hK⟩ := H1 ν hν (hle.trans (min_le_left _ _)) tr htr ℓ j
  obtain ⟨b, C₀, C', C, N, hb, hC₀, hC', hC, hT⟩ :=
    H2 ν hν (hle.trans (min_le_right _ _)) tr htr ℓ j
  set A : ℝ := C' / ν + 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set E : ℝ := Real.exp b * (m.factorial / b ^ m) +
    Real.exp (b / C₀) * (m.factorial * (2 * (C₀ + ν) / b) ^ m) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨(1 + A) ^ m * |K| + (1 + A) ^ m * C * E, N + m, fun s hs z => ?_⟩
  set f := ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean (trainPeriod ρ ν) (tr.ψ r) w.2) s z‖ with hf
  have hf0 : 0 ≤ f := norm_nonneg _
  have hs1 : (1 : ℝ) ≤ (1 + s) ^ (N + m) := one_le_pow₀ (by linarith)
  have hsp : (0 : ℝ) ≤ (1 + s) ^ (N + m) := by positivity
  by_cases hz : A ≤ |z.2|
  · -- outer region
    set l := |z.2| - A with hl
    have hl0 : 0 ≤ l := by linarith
    have hzl : C' / ν + 2 + l ≤ |z.2| := by rw [hl, hA]; linarith
    have ht := hT s hs.le l hl0 s hs le_rfl z hzl
    have hw : (1 + |z.2|) ^ m ≤ (1 + A) ^ m * (1 + l) ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : |z.2| = A + l := by rw [hl]; ring
      rw [this]; nlinarith [mul_nonneg hA0 hl0]
    set D := C₀ + ν * s with hD
    have hD1 : C₀ ≤ D := by rw [hD]; nlinarith [mul_pos hν hs]
    have hDle : D ≤ (C₀ + ν) * (1 + s) := by rw [hD]; nlinarith [mul_pos hν hs, hC₀]
    have c1 := core1 m hb hl0
    have c2 := core2 m hb hC₀ hD1 hl0
    have hpow : (2 * D / b) ^ m ≤ (2 * ((C₀ + ν) * (1 + s)) / b) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      have : 2 * D / b ≤ 2 * ((C₀ + ν) * (1 + s)) / b := by
        apply div_le_div_of_nonneg_right _ hb.le
        linarith
      exact this
    have hpow' : (2 * ((C₀ + ν) * (1 + s)) / b) ^ m = (2 * (C₀ + ν) / b) ^ m * (1 + s) ^ m := by
      rw [← mul_pow]; congr 1; ring
    have hexp0 : 0 ≤ Real.exp (-(b * l)) := (Real.exp_pos _).le
    have hexp1 : 0 ≤ Real.exp (-(b * l ^ 2 / D)) := (Real.exp_pos _).le
    have hsm : (1 : ℝ) ≤ (1 + s) ^ m := one_le_pow₀ (by linarith)
    -- the weighted sum
    have hsum : (1 + l) ^ m * (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / D))) ≤
        E * (1 + s) ^ m := by
      rw [mul_add]
      have e1 : (1 + l) ^ m * Real.exp (-(b * l)) ≤
          (Real.exp b * (m.factorial / b ^ m)) * (1 + s) ^ m := by
        have : 0 ≤ Real.exp b * (m.factorial / b ^ m) := by positivity
        nlinarith
      have e2 : (1 + l) ^ m * Real.exp (-(b * l ^ 2 / D)) ≤
          (Real.exp (b / C₀) * (m.factorial * (2 * (C₀ + ν) / b) ^ m)) * (1 + s) ^ m := by
        calc _ ≤ Real.exp (b / C₀) * (m.factorial * (2 * D / b) ^ m) := c2
          _ ≤ Real.exp (b / C₀) * (m.factorial * ((2 * (C₀ + ν) / b) ^ m * (1 + s) ^ m)) := by
              rw [← hpow']
              gcongr
          _ = _ := by ring
      rw [hE]; nlinarith
    have hf' : f ≤ C * (1 + s) ^ N *
        (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / D))) := ht
    calc (1 + |z.2|) ^ m * f
        ≤ ((1 + A) ^ m * (1 + l) ^ m) * (C * (1 + s) ^ N *
            (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / D)))) := by
          apply mul_le_mul hw hf' hf0 (by positivity)
      _ = (1 + A) ^ m * C * (1 + s) ^ N *
            ((1 + l) ^ m * (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / D)))) := by ring
      _ ≤ (1 + A) ^ m * C * (1 + s) ^ N * (E * (1 + s) ^ m) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (1 + A) ^ m * C * E * (1 + s) ^ (N + m) := by rw [pow_add]; ring
      _ ≤ ((1 + A) ^ m * |K| + (1 + A) ^ m * C * E) * (1 + s) ^ (N + m) := by
          refine mul_le_mul_of_nonneg_right ?_ hsp
          have : 0 ≤ (1 + A) ^ m * |K| := by positivity
          linarith
  · -- core region
    have hz' : |z.2| ≤ A := (not_le.1 hz).le
    have hw : (1 + |z.2|) ^ m ≤ (1 + A) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    have hfK : f ≤ |K| := by
      have := hK s hs z
      have h3 : K * Real.exp (-(κ * s)) ≤ |K| := by
        calc K * Real.exp (-(κ * s)) ≤ |K| * Real.exp (-(κ * s)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
          _ ≤ |K| * 1 := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              rw [Real.exp_le_one_iff]; nlinarith
          _ = |K| := mul_one _
      linarith
    calc (1 + |z.2|) ^ m * f ≤ (1 + A) ^ m * |K| :=
          mul_le_mul hw hfK hf0 (by positivity)
      _ = (1 + A) ^ m * |K| * 1 := by ring
      _ ≤ (1 + A) ^ m * |K| * (1 + s) ^ (N + m) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ ≤ ((1 + A) ^ m * |K| + (1 + A) ^ m * C * E) * (1 + s) ^ (N + m) := by
          refine mul_le_mul_of_nonneg_right ?_ hsp
          have : 0 ≤ (1 + A) ^ m * C * E := by positivity
          linarith


/-- **Leaf (a)-(c): transverse tail of the vorticity jets at fixed parameters** (SP 460-467 for
`ω`, proof 481-494: the vorticity drift-diffusion equation `ω_s + v·∇ω - νΔω = 0`, the Gaussian
datum and the supersolutions `C exp{-λ(η-A(s)) + (C₀+νs)λ²}`, `A(s) = ∫₀ˢ ‖v₂(t)‖_∞ dt ≤ C/ν`
(from `sct:train`), with both transverse signs, give `|ω| ≤ C exp[-b(|η|-C/ν)₊²/(C₀+νs)]`;
unit-patch interpolation with the fixed higher bounds gives the same tail for every derivative; age
derivatives through the vorticity equation; fixed parameters SP 427-435).  For `ρ > 1/2` one `ν₀`;
for every BUC train with `ν ≤ ν₀` and all `ℓ, j` there are constants (depending on the train) with
`‖∂_s^ℓ D^j ω(s, z)‖ ≤ C(1+S)^N {e^{-b l} + e^{-b l²/(C₀+νS)}}` for `0 < s ≤ S`, `l ≥ 0`,
`|η| ≥ C'/ν + 2 + l`. -/
def VortJetTailFixed : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ ℓ j : ℕ,
      ∃ b C₀ C' C : ℝ, ∃ N : ℕ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧
        ∀ S_ : ℝ, 0 ≤ S_ → ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane,
          C' / ν + 2 + l ≤ |z.2| →
            ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
              C * (1 + S_) ^ N *
                (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))

/-- **Leaf (d), calculus of the stream fluctuation jets** (SP 496-502: `ω = Δψ` for `v = ∇^⊥ψ`,
the fluctuation `ψ̃ = ψ - \bar ψ` consists of the nonzero `q`-modes).  For a BUC train, `s > 0`
and a fixed tuple `u`, the component `W_u(z) = (∂_s^ℓ D^j ψ̃)(s, z)(u)` is `C²` and `c`-periodic in
`q`, has zero `q`-mean on every slice, its `q`-derivative is the component
`(∂_s^ℓ D^{j+1} ψ̃)(s, z)(e_q, u)` of the next jet, and
`Δ W_u = (∂_s^ℓ D^j ω)(s, z)(u) + h(η)` for a function `h` of `η` alone (the jet of `-\bar ψ''`;
`ψ` is jointly smooth for `s > 0`, `PartI.trainStreamSmooth`; `ψ` is periodic because `v` is and
`ψ` decays; `Δψ = curl ∇^⊥ψ = ω`). -/
def FluctJetCalc : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    ∀ ℓ j : ℕ, ∀ s : ℝ, 0 < s → ∀ u : Fin j → Plane,
      ContDiff ℝ 2 (fun z : Plane =>
          ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z u) ∧
      Cyl.IsPeriodic c (fun z : Plane =>
          ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z u) ∧
      (∀ η : ℝ, ∫ q in Ioc (-c / 2) (c / 2),
          ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s (q, η) u = 0) ∧
      (∀ z : Plane, Cyl.partialQ (fun z' : Plane =>
          ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z' u) z =
        ageJet ℓ (j + 1) (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z
          (Fin.cons ((1 : ℝ), (0 : ℝ)) u)) ∧
      ∃ h : ℝ → ℝ, ∀ z : Plane,
        Train.lapS (fun z' : Plane =>
            ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z' u) z =
          ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z u + h z.2

namespace FluctTail

/-- Monotonicity of the tail form in its constants. -/
theorem tail_mono {b b' C₀ C₀' C C' ν S x : ℝ} {N N' : ℕ} (hb : 0 < b) (hbb : b ≤ b')
    (hC0 : 0 < C₀') (hCC0 : C₀' ≤ C₀) (hC : 0 ≤ C') (hCC : C' ≤ C) (hNN : N' ≤ N)
    (hS : 0 ≤ S) (hν : 0 < ν) (hx : 0 ≤ x) :
    C' * (1 + S) ^ N' * (Real.exp (-(b' * x)) + Real.exp (-(b' * x ^ 2 / (C₀' + ν * S)))) ≤
      C * (1 + S) ^ N * (Real.exp (-(b * x)) + Real.exp (-(b * x ^ 2 / (C₀ + ν * S)))) := by
  have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
  have hp : (1 + S) ^ N' ≤ (1 + S) ^ N := pow_le_pow_right₀ hS1 hNN
  have hD' : 0 < C₀' + ν * S := add_pos_of_pos_of_nonneg hC0 (mul_nonneg hν.le hS)
  have hD : C₀' + ν * S ≤ C₀ + ν * S := by linarith
  have e1 : Real.exp (-(b' * x)) ≤ Real.exp (-(b * x)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have e2 : Real.exp (-(b' * x ^ 2 / (C₀' + ν * S))) ≤ Real.exp (-(b * x ^ 2 / (C₀ + ν * S))) := by
    apply Real.exp_le_exp.2
    have h1 : b / (C₀ + ν * S) ≤ b' / (C₀' + ν * S) := div_le_div₀ (by linarith) hbb hD' hD
    have h2 : b * x ^ 2 / (C₀ + ν * S) = b / (C₀ + ν * S) * x ^ 2 := by ring
    have h3 : b' * x ^ 2 / (C₀' + ν * S) = b' / (C₀' + ν * S) * x ^ 2 := by ring
    rw [h2, h3]
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg x)
    linarith
  have hsum : Real.exp (-(b' * x)) + Real.exp (-(b' * x ^ 2 / (C₀' + ν * S))) ≤
      Real.exp (-(b * x)) + Real.exp (-(b * x ^ 2 / (C₀ + ν * S))) := add_le_add e1 e2
  have hpos : 0 ≤ Real.exp (-(b' * x)) + Real.exp (-(b' * x ^ 2 / (C₀' + ν * S))) := by
    positivity
  calc C' * (1 + S) ^ N' * (Real.exp (-(b' * x)) + Real.exp (-(b' * x ^ 2 / (C₀' + ν * S))))
      ≤ C * (1 + S) ^ N * (Real.exp (-(b' * x)) + Real.exp (-(b' * x ^ 2 / (C₀' + ν * S)))) := by
        apply mul_le_mul_of_nonneg_right _ hpos
        exact mul_le_mul hCC hp (pow_nonneg (by linarith) _) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))

/-- `|a| ≤ B` from `a² ≤ K (X² + Y²)` with `1 ≤ K`, `X, Y ≥ 0`, `B = K (X + Y)`. -/
theorem abs_le_of_sq_le_sum {a K X Y : ℝ} (hK : 1 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : a ^ 2 ≤ K * (X ^ 2 + Y ^ 2)) : |a| ≤ K * (X + Y) := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 : X ^ 2 + Y ^ 2 ≤ (X + Y) ^ 2 := by nlinarith
  have h2 : K * (X + Y) ^ 2 ≤ K ^ 2 * (X + Y) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  calc a ^ 2 ≤ K * (X ^ 2 + Y ^ 2) := h
    _ ≤ K * (X + Y) ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ K ^ 2 * (X + Y) ^ 2 := h2
    _ = (K * (X + Y)) ^ 2 := by ring

end FluctTail

set_option maxHeartbeats 1600000 in
/-- **The core estimate at a fixed train** (step (d) of SP 496-502, all nonzero modes at once in
`L²` on the slices): from the vorticity tails of the orders `j, j+1`, uniform bounds of the
fluctuation jets of the orders `j, j+1` and the jet calculus, the fluctuation jet of order `j` has
the transverse tail. -/
theorem FluctTail.fluct_tail_core (hC : FluctJetCalc) {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (htr : IsBUCTrain tr) (ℓ j : ℕ)
    (HV : ∀ k : ℕ, ∃ b C₀ C' C : ℝ, ∃ N : ℕ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧
      ∀ S_ : ℝ, 0 ≤ S_ → ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane,
        C' / ν + 2 + l ≤ |z.2| →
          ‖ageJet ℓ k (fun r w => Cyl.curl (tr.v r) w) s z‖ ≤
            C * (1 + S_) ^ N *
              (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))))
    (HA : ∀ k : ℕ, ∃ M : ℝ, ∀ s : ℝ, 0 < s → ∀ z : Plane,
      ‖ageJet ℓ k (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖ ≤ M) :
    ∃ b C₀ C' C : ℝ, ∃ N : ℕ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧ 0 < C ∧
      ∀ S_ : ℝ, 0 ≤ S_ → ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane,
        C' / ν + 2 + l ≤ |z.2| →
          ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖ ≤
            C * (1 + S_) ^ N *
              (Real.exp (-(b * l)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_)))) := by
  obtain ⟨b1, C01, C'1, C1, N1, hb1, hC01, hC'1, hC1, T1⟩ := HV j
  obtain ⟨b2, C02, C'2, C2, N2, hb2, hC02, hC'2, hC2, T2⟩ := HV (j + 1)
  obtain ⟨K1, A1⟩ := HA j
  obtain ⟨K2, A2⟩ := HA (j + 1)
  set lam : ℝ := 2 * π / c with hlam_def
  have hlam : 0 < lam := by positivity
  set b : ℝ := min b1 b2 with hb_def
  have hb : 0 < b := lt_min hb1 hb2
  set C₀ : ℝ := max C01 C02 with hC0_def
  have hC0 : 0 < C₀ := lt_max_of_lt_left hC01
  set C' : ℝ := max C'1 C'2 with hC'_def
  have hC' : 0 < C' := lt_max_of_lt_left hC'1
  set Cω : ℝ := max C1 C2 with hCω_def
  have hCω : 0 < Cω := lt_max_of_lt_left hC1
  set N : ℕ := max N1 N2 with hN_def
  set M0 : ℝ := max |K1| |K2| with hM0_def
  have hM0 : 0 ≤ M0 := le_max_of_le_left (abs_nonneg _)
  set bt : ℝ := min (lam / 4) (b / 4) with hbt_def
  have hbt : 0 < bt := lt_min (by positivity) (by positivity)
  set κc : ℝ := 2 + c ^ 2 with hκc_def
  have hκc : 1 ≤ κc := by rw [hκc_def]; nlinarith [sq_nonneg c]
  have hCt : 0 < κc * M0 + κc / lam ^ 2 * Cω := by
    have h1 : 0 ≤ κc * M0 := mul_nonneg (by linarith) hM0
    have h2 : 0 < κc / lam ^ 2 * Cω := mul_pos (div_pos (by linarith) (by positivity)) hCω
    linarith
  refine ⟨bt, C₀, C', κc * M0 + κc / lam ^ 2 * Cω, N, hbt, hC0, hC', hCt,
    fun S_ hS l hl s hs hsS z hz => ?_⟩
  set D : ℝ := C₀ + ν * S_ with hD_def
  have hD : 0 < D := add_pos_of_pos_of_nonneg hC0 (mul_nonneg hν.le hS)
  set ε : ℝ := Cω * (1 + S_) ^ N *
    (Real.exp (-(b * (l / 2))) + Real.exp (-(b * (l / 2) ^ 2 / D))) with hε_def
  have hε : 0 ≤ ε := mul_nonneg (mul_nonneg hCω.le (pow_nonneg (by linarith) _)) (by positivity)
  set η₁ : ℝ := C' / ν + 2 + l / 2 with hη₁_def
  -- the vorticity jets beyond `η₁`
  have hl2 : 0 ≤ l / 2 := by positivity
  have hω1 : ∀ z' : Plane, η₁ ≤ |z'.2| →
      ‖ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z'‖ ≤ ε := by
    intro z' hz'
    have hz1 : C'1 / ν + 2 + l / 2 ≤ |z'.2| := by
      have : C'1 / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_left _ _) hν.le
      linarith
    have h := T1 S_ hS (l / 2) hl2 s hs hsS z' hz1
    exact h.trans (FluctTail.tail_mono hb (min_le_left _ _) hC01 (le_max_left _ _) hC1.le
      (le_max_left _ _) (le_max_left _ _) hS hν hl2)
  have hω2 : ∀ z' : Plane, η₁ ≤ |z'.2| →
      ‖ageJet ℓ (j + 1) (fun r w => Cyl.curl (tr.v r) w) s z'‖ ≤ ε := by
    intro z' hz'
    have hz1 : C'2 / ν + 2 + l / 2 ≤ |z'.2| := by
      have : C'2 / ν ≤ C' / ν := div_le_div_of_nonneg_right (le_max_right _ _) hν.le
      linarith
    have h := T2 S_ hS (l / 2) hl2 s hs hsS z' hz1
    exact h.trans (FluctTail.tail_mono hb (min_le_right _ _) hC02 (le_max_right _ _) hC2.le
      (le_max_right _ _) (le_max_right _ _) hS hν hl2)
  -- the fluctuation jets are bounded by `M0`
  have hψ1 : ∀ z' : Plane,
      ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z'‖ ≤ M0 :=
    fun z' => (A1 s hs z').trans ((le_abs_self _).trans (le_max_left _ _))
  have hψ2 : ∀ z' : Plane,
      ‖ageJet ℓ (j + 1) (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z'‖ ≤ M0 :=
    fun z' => (A2 s hs z').trans ((le_abs_self _).trans (le_max_right _ _))
  -- the point `z` is at distance `≥ l/2` beyond `η₁`
  have hzη : η₁ ≤ |z.2| := by
    have : l / 2 ≤ l := by linarith
    linarith
  have hgap : l / 2 ≤ |z.2| - η₁ := by linarith
  set E4 : ℝ := Real.exp (-(lam * l / 4)) with hE4_def
  have hE4 : 0 ≤ E4 := (Real.exp_pos _).le
  have hgapE : Real.exp (-(lam * (|z.2| - η₁))) ≤ E4 ^ 2 := by
    rw [hE4_def, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hgap hlam.le
    push_cast
    linarith
  have heq : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
  -- the componentwise bound
  set Bd : ℝ := κc * (M0 * E4 + ε / lam ^ 2) with hBd_def
  have hBd : 0 ≤ Bd := mul_nonneg (by linarith)
    (add_nonneg (mul_nonneg hM0 hE4) (div_nonneg hε (by positivity)))
  have hcomp : ∀ u : Fin j → Plane,
      ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z u‖ ≤
        Bd * ∏ i, ‖u i‖ := by
    intro u
    set P : ℝ := ∏ i, ‖u i‖ with hP_def
    have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => norm_nonneg _)
    obtain ⟨hW2, hWper, hWmean, hWq, h0, hWlap⟩ := hC ν c hν hc tr htr ℓ j s hs u
    obtain ⟨hW12, hW1per, hW1mean, -, h1, hW1lap⟩ :=
      hC ν c hν hc tr htr ℓ (j + 1) s hs (Fin.cons ((1 : ℝ), (0 : ℝ)) u)
    have hPc : ∏ i, ‖(Fin.cons ((1 : ℝ), (0 : ℝ)) u : Fin (j + 1) → Plane) i‖ = P := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, heq, one_mul]
      exact hP_def.symm
    have hM : ∀ z' : Plane, η₁ ≤ |z'.2| →
        |ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z' u| ≤ M0 * P := by
      intro z' _
      rw [← Real.norm_eq_abs]
      exact ((ContinuousMultilinearMap.le_opNorm _ u)).trans
        (mul_le_mul_of_nonneg_right (hψ1 z') hP)
    have hM₁ : ∀ z' : Plane, η₁ ≤ |z'.2| →
        |ageJet ℓ (j + 1) (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z'
          (Fin.cons ((1 : ℝ), (0 : ℝ)) u)| ≤ M0 * P := by
      intro z' _
      rw [← Real.norm_eq_abs, ← hPc]
      exact ((ContinuousMultilinearMap.le_opNorm _ _)).trans
        (mul_le_mul_of_nonneg_right (hψ2 z') (Finset.prod_nonneg (fun i _ => norm_nonneg _)))
    have hf : ∀ z' : Plane, η₁ ≤ |z'.2| →
        |ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s z' u| ≤ ε * P := by
      intro z' hz'
      rw [← Real.norm_eq_abs]
      exact ((ContinuousMultilinearMap.le_opNorm _ u)).trans
        (mul_le_mul_of_nonneg_right (hω1 z' hz') hP)
    have hf₁ : ∀ z' : Plane, η₁ ≤ |z'.2| →
        |ageJet ℓ (j + 1) (fun r w => Cyl.curl (tr.v r) w) s z'
          (Fin.cons ((1 : ℝ), (0 : ℝ)) u)| ≤ ε * P := by
      intro z' hz'
      rw [← Real.norm_eq_abs, ← hPc]
      exact ((ContinuousMultilinearMap.le_opNorm _ _)).trans
        (mul_le_mul_of_nonneg_right (hω2 z' hz') (Finset.prod_nonneg (fun i _ => norm_nonneg _)))
    have hsq := UnforcedLeray.Short.PartIIIb.Concrete.FluctTail.zeroMean_sq_tail hc hW2 hW12 hWper hW1per hWmean hW1mean hWq
      hWlap hW1lap hM hM₁ hf hf₁ z hzη
    rw [← hlam_def, ← hκc_def] at hsq
    have hsq' : (ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z u) ^ 2 ≤
        κc * ((M0 * P * E4) ^ 2 + (ε * P / lam ^ 2) ^ 2) := by
      refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      have h1 : (M0 * P) ^ 2 * Real.exp (-(lam * (|z.2| - η₁))) ≤ (M0 * P * E4) ^ 2 := by
        rw [mul_pow (M0 * P) E4]
        exact mul_le_mul_of_nonneg_left hgapE (sq_nonneg _)
      have h2 : (ε * P) ^ 2 / lam ^ 4 = (ε * P / lam ^ 2) ^ 2 := by
        ring
      linarith
    have hab := FluctTail.abs_le_of_sq_le_sum hκc (by positivity) (by positivity) hsq'
    rw [Real.norm_eq_abs]
    calc |ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z u|
        ≤ κc * (M0 * P * E4 + ε * P / lam ^ 2) := hab
      _ = Bd * P := by rw [hBd_def]; ring
  have hnorm : ‖ageJet ℓ j (fun r w => tr.ψ r w - hmean c (tr.ψ r) w.2) s z‖ ≤ Bd :=
    ContinuousMultilinearMap.opNorm_le_bound hBd hcomp
  -- the final comparison with the tail form
  refine hnorm.trans ?_
  set X : ℝ := Real.exp (-(bt * l)) + Real.exp (-(bt * l ^ 2 / D)) with hX_def
  have hS1 : (1 : ℝ) ≤ (1 + S_) ^ N := one_le_pow₀ (by linarith)
  have eA : E4 ≤ Real.exp (-(bt * l)) := by
    rw [hE4_def]
    apply Real.exp_le_exp.2
    have : bt ≤ lam / 4 := min_le_left _ _
    nlinarith
  have eB : Real.exp (-(b * (l / 2))) ≤ Real.exp (-(bt * l)) := by
    apply Real.exp_le_exp.2
    have : bt ≤ b / 4 := min_le_right _ _
    nlinarith
  have eC : Real.exp (-(b * (l / 2) ^ 2 / D)) ≤ Real.exp (-(bt * l ^ 2 / D)) := by
    apply Real.exp_le_exp.2
    have hbt4 : bt ≤ b / 4 := min_le_right _ _
    have h1 : bt * l ^ 2 / D ≤ b * (l / 2) ^ 2 / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      nlinarith [sq_nonneg l]
    linarith
  have hX1 : Real.exp (-(bt * l)) ≤ X := by
    rw [hX_def]; linarith [Real.exp_pos (-(bt * l ^ 2 / D))]
  have hX0 : 0 ≤ X := by positivity
  have hεX : ε ≤ Cω * (1 + S_) ^ N * X := by
    rw [hε_def]
    apply mul_le_mul_of_nonneg_left (add_le_add eB eC)
      (mul_nonneg hCω.le (pow_nonneg (by linarith) _))
  have hfirst : M0 * E4 ≤ M0 * ((1 + S_) ^ N * X) := by
    apply mul_le_mul_of_nonneg_left _ hM0
    calc E4 ≤ X := eA.trans hX1
      _ = 1 * X := (one_mul X).symm
      _ ≤ (1 + S_) ^ N * X := mul_le_mul_of_nonneg_right hS1 hX0
  have hκ0 : 0 ≤ κc := by linarith
  have hl2' : 0 < lam ^ 2 := by positivity
  calc Bd = κc * (M0 * E4) + κc / lam ^ 2 * ε := by rw [hBd_def]; ring
    _ ≤ κc * (M0 * ((1 + S_) ^ N * X)) + κc / lam ^ 2 * (Cω * (1 + S_) ^ N * X) := by
        gcongr
    _ = (κc * M0 + κc / lam ^ 2 * Cω) * (1 + S_) ^ N * X := by ring


/-- **`FluctTransverseTailFixed` from the vorticity tail** (step (d) of SP 496-502, all nonzero
modes at once in `L²` on the slices; leaves `VortJetTailFixed` (steps (a)-(c)),
`PartI.TrainFluctAgeJetFixed`, `FluctJetCalc`). -/
theorem fluctTransverseTailFixed_of (hV : VortJetTailFixed) (hA : TrainFluctAgeJetFixed)
    (hC : FluctJetCalc) : FluctTransverseTailFixed := by
  intro ρ hρ
  obtain ⟨ν1, hν1, HV⟩ := hV ρ hρ
  obtain ⟨ν2, hν2, HA⟩ := hA ρ hρ
  refine ⟨min ν1 ν2, lt_min hν1 hν2, fun ν hν hle tr htr ℓ j => ?_⟩
  have hle1 : ν ≤ ν1 := hle.trans (min_le_left _ _)
  have hle2 : ν ≤ ν2 := hle.trans (min_le_right _ _)
  have hc : 0 < trainPeriod ρ ν := Real.rpow_pos_of_pos hν _
  refine FluctTail.fluct_tail_core hC hν hc tr htr ℓ j (fun k => HV ν hν hle1 tr htr ℓ k)
    (fun k => ?_)
  obtain ⟨C, κ, hκ, hCk⟩ := HA ν hν hle2 tr htr ℓ k
  refine ⟨|C|, fun s hs z => (hCk s hs z).trans ?_⟩
  calc C * Real.exp (-(κ * s)) ≤ |C| * Real.exp (-(κ * s)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |C| * 1 := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [Real.exp_le_one_iff]; nlinarith
    _ = |C| := mul_one _


end UnforcedLeray.Short.IIb.WeightedTrainFluctAux
