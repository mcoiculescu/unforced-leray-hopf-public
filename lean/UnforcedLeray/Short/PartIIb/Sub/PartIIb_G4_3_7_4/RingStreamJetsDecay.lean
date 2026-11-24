import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4

/-!
# Part II-b, task `PartII-b:G4/3/7/4/1` (`RingStreamJetsDecay`)

Source of record: `the November 2 reference manuscript`, lines 2360-2369.
`ringStreamProfile R φ = (-φ_η, φ_q + R⁻¹(φ - 2sφ_s - ηφ_η))`. Derivatives of order `≤ j` of the
profile are bounded by `C(j)` times the derivatives of `φ` of order `≤ j+1` (Leibniz for the
coefficients `s`, `η`, `R⁻¹`), and the factor `|η| e^{-κ|η|/c'}` is absorbed into the halved
decay rate `e^{-κ|η|/(2c')}` by `|η| e^{-u} ≤ 2(1 + c'/κ) e^{-u/2}`, `u = κ|η|/c'`.
The support clauses give `∂_s φ(x) = 0` for `|s| > S`, so the factor `s` on `∂_s φ` costs `S`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace RingStreamJetsDecayAux

abbrev E3 := ℝ × (ℝ × ℝ)

theorem cdAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E3) : ContDiffAt ℝ n f x :=
  hf.contDiffAt.of_le (by exact_mod_cast le_top)

theorem apply_norm_le (v : E3) : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact f.le_opNorm v

theorem iter_dir (f : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (v : E3) (k : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℝ v)
    (f := fderiv ℝ f) (x := x) (N := ∞) (n := k) hD.contDiffAt (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_mul_of_nonneg_right (apply_norm_le v) (norm_nonneg _))

theorem sum_range_two (F : ℕ → ℝ) (hF : ∀ i, 2 ≤ i → F i = 0) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), F i = F 0 + F 1 := by
  induction n with
  | zero => simp [Finset.sum_range_succ]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Finset.sum_range_succ, ih, hF (n + 2) (by omega)]
    ring

theorem iter_clm_two (L : E3 →L[ℝ] ℝ) (k : ℕ) (x : E3) :
    iteratedFDeriv ℝ (k + 2) (⇑L) x = 0 := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (⇑L : E3 → ℝ)) (x := x) (n := k + 1)
  have hd : fderiv ℝ (⇑L : E3 → ℝ) = fun _ => L := funext fun y => L.fderiv
  rw [hd, iteratedFDeriv_succ_const] at h
  have h' : ‖iteratedFDeriv ℝ (k + 1 + 1) (⇑L : E3 → ℝ) x‖ = 0 := by
    rw [← h]; simp
  exact norm_eq_zero.mp h'

theorem iter_clm_one (L : E3 →L[ℝ] ℝ) (x : E3) :
    ‖iteratedFDeriv ℝ 1 (⇑L) x‖ = ‖L‖ := by
  rw [norm_iteratedFDeriv_one, L.fderiv]

theorem norm_iter_mul_clm (L : E3 →L[ℝ] ℝ) (g : E3 → ℝ) (hg : ContDiff ℝ ∞ g) (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => L y * g y) x‖ ≤
      ‖L x‖ * ‖iteratedFDeriv ℝ l g x‖ + (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) g x‖ := by
  cases l with
  | zero => simp [norm_mul]
  | succ n =>
    have hL : ContDiff ℝ ∞ (⇑L : E3 → ℝ) := L.contDiff
    have hmul := norm_iteratedFDeriv_mul_le hL hg x (n := n + 1) (by exact_mod_cast le_top)
    have hF2 : ∀ i, 2 ≤ i → (((n + 1).choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i (⇑L : E3 → ℝ) x‖ *
        ‖iteratedFDeriv ℝ (n + 1 - i) g x‖ = 0 := by
      intro i hi
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [iter_clm_two L k x]
      simp
    have hsum := sum_range_two (fun i => (((n + 1).choose i : ℕ) : ℝ) *
        ‖iteratedFDeriv ℝ i (⇑L : E3 → ℝ) x‖ * ‖iteratedFDeriv ℝ (n + 1 - i) g x‖) hF2 n
    have e0 : ‖iteratedFDeriv ℝ 0 (⇑L : E3 → ℝ) x‖ = ‖L x‖ := norm_iteratedFDeriv_zero
    have e1 : ‖iteratedFDeriv ℝ 1 (⇑L : E3 → ℝ) x‖ = ‖L‖ := iter_clm_one L x
    calc ‖iteratedFDeriv ℝ (n + 1) (fun y => L y * g y) x‖
        ≤ ∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : ℝ) *
            ‖iteratedFDeriv ℝ i (⇑L : E3 → ℝ) x‖ * ‖iteratedFDeriv ℝ (n + 1 - i) g x‖ := hmul
      _ = ‖L x‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖ + ((n + 1 : ℕ) : ℝ) * ‖L‖ *
            ‖iteratedFDeriv ℝ n g x‖ := by
          rw [show n + 1 + 1 = n + 2 by ring, hsum]
          have hn1 : n + 1 - 1 = n := by omega
          simp only [e0, e1, Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero,
            Nat.cast_one, Nat.cast_add]
          rw [hn1]
          push_cast
          ring
      _ = _ := by simp

theorem iter_smul_vec {M' : Type*} [NormedAddCommGroup M'] [NormedSpace ℝ M']
    (c : E3 → ℝ) (hc : ContDiff ℝ ∞ c) (u : M') (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => c y • u) x‖ ≤ ‖u‖ * ‖iteratedFDeriv ℝ l c x‖ := by
  let T : ℝ →L[ℝ] M' := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) u
  have hT : ‖T‖ ≤ ‖u‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun t => by
    simp only [T, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, norm_smul]
    rw [mul_comm])
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left T (f := c) (x := x) (N := ∞)
    (n := l) hc.contDiffAt (by exact_mod_cast le_top)
  have hfun : (fun y => c y • u) = T ∘ c := by
    funext y
    simp [T]
  rw [hfun]
  exact h.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

theorem iter_vec_add {M' : Type*} [NormedAddCommGroup M'] [NormedSpace ℝ M']
    (a b : E3 → ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (v w : M') (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => a y • v + b y • w) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ l a x‖ + ‖w‖ * ‖iteratedFDeriv ℝ l b x‖ := by
  have hA : ContDiff ℝ ∞ (fun y => a y • v) := ha.smul contDiff_const
  have hB : ContDiff ℝ ∞ (fun y => b y • w) := hb.smul contDiff_const
  have hfun : (fun y => a y • v + b y • w) = (fun y => a y • v) + (fun y => b y • w) := rfl
  rw [hfun, iteratedFDeriv_add_apply (cdAt hA l x) (cdAt hB l x)]
  exact (norm_add_le _ _).trans (add_le_add (iter_smul_vec a ha v l x) (iter_smul_vec b hb w l x))

theorem iter_add' (f g : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
  have hfun : (fun y => f y + g y) = f + g := rfl
  rw [hfun, iteratedFDeriv_add_apply (cdAt hf l x) (cdAt hg l x)]
  exact norm_add_le _ _

theorem iter_sub' (f g : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
  have hfun : (fun y => f y - g y) = f - g := rfl
  rw [hfun, iteratedFDeriv_sub_apply (cdAt hf l x) (cdAt hg l x)]
  exact norm_sub_le _ _

theorem iter_cmul' (c : ℝ) (f : E3 → ℝ) (hf : ContDiff ℝ ∞ f) (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => c * f y) x‖ ≤ ‖c‖ * ‖iteratedFDeriv ℝ l f x‖ := by
  have hfun : (fun y => c * f y) = fun y => c • f y := by funext y; simp [smul_eq_mul]
  rw [hfun, iteratedFDeriv_const_smul_apply' (cdAt hf l x), norm_smul]

theorem support_dS (φ : E3 → ℝ) (S : ℝ)
    (h1 : ∀ x : E3, S < x.1 → φ x = 0)
    (h2 : ∀ x : E3, x.1 < -S → fderiv ℝ φ x (1, (0, 0)) = 0) (k : ℕ) (x : E3)
    (hx : S < |x.1|) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ φ y (1, (0, 0))) x = 0 := by
  have hev : (fun y => fderiv ℝ φ y (1, (0, 0))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    rcases lt_abs.mp hx with h | h
    · have hU : IsOpen {y : E3 | S < y.1} := isOpen_lt continuous_const continuous_fst
      filter_upwards [hU.mem_nhds (show x ∈ {y : E3 | S < y.1} from h)] with y hy
      have hφ0 : φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hU.mem_nhds (show y ∈ {y : E3 | S < y.1} from hy)] with z hz
        exact h1 z hz
      rw [hφ0.fderiv_eq]
      simp
    · have hU : IsOpen {y : E3 | y.1 < -S} := isOpen_lt continuous_fst continuous_const
      filter_upwards [hU.mem_nhds (show x ∈ {y : E3 | y.1 < -S} from by
        show x.1 < -S
        linarith)] with y hy
      exact h2 y hy
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  simp

theorem exp_le_exp_half (η κ c' : ℝ) (hκ : 0 < κ) (hc : 0 < c') :
    Real.exp (-(κ * |η| / c')) ≤ Real.exp (-((κ / 2) * |η| / c')) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_right _ hc.le
  nlinarith [abs_nonneg η]

theorem exp_decay_bound (η κ c' : ℝ) (hκ : 0 < κ) (hc : 0 < c') :
    |η| * Real.exp (-(κ * |η| / c')) ≤
      2 * (1 + c' / κ) * Real.exp (-((κ / 2) * |η| / c')) := by
  have hκ0 := hκ.ne'
  have hc0 := hc.ne'
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (κ / 2) * |η| / c' := ⟨_, rfl⟩
  rw [← hx]
  have hE : Real.exp (-(κ * |η| / c')) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; rw [hx]; ring
  have hη : |η| = (c' / κ) * (2 * x) := by
    rw [hx]; field_simp
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hG : 0 < Real.exp (-x) := Real.exp_pos _
  have hc' : 0 ≤ c' / κ := by positivity
  have hxe : x * Real.exp (-x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have h2 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  rw [hE, hη]
  have h6 : c' / κ * (2 * x) * (Real.exp (-x) * Real.exp (-x)) =
      (c' / κ) * (2 * (x * Real.exp (-x))) * Real.exp (-x) := by ring
  rw [h6]
  have h7 : 2 * (x * Real.exp (-x)) ≤ 2 := by linarith
  have h8 : (c' / κ) * (2 * (x * Real.exp (-x))) ≤ (c' / κ) * 2 :=
    mul_le_mul_of_nonneg_left h7 hc'
  have h9 : (c' / κ) * (2 * (x * Real.exp (-x))) * Real.exp (-x) ≤
      (c' / κ) * 2 * Real.exp (-x) := mul_le_mul_of_nonneg_right h8 hG.le
  nlinarith [hG, hc']

theorem iter_neg' (f : E3 → ℝ) (l : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ l (fun y => -(f y)) x‖ = ‖iteratedFDeriv ℝ l f x‖ := by
  have hfun : (fun y => -(f y)) = -f := rfl
  rw [hfun, iteratedFDeriv_neg_apply, norm_neg]

end RingStreamJetsDecayAux

open RingStreamJetsDecayAux in
theorem ringStreamJetsDecay : UnforcedLeray.Short.IIb.RingStreamJetsDecay := by
  intro j
  refine ⟨10 * ((j : ℝ) + 1), by positivity, ?_⟩
  intro R S c' κ M φ hR hS hc hκ hM hφ hφS hφ' hbd l hl m
  obtain ⟨B, hB⟩ : ∃ B : E3 → ℝ, B = fun y => M * Real.exp (-(κ * |y.2.2| / c')) :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : E3 → ℝ, G = fun y => Real.exp (-((κ / 2) * |y.2.2| / c')) :=
    ⟨_, rfl⟩
  have hB0 : ∀ y, 0 ≤ B y := fun y => by simp only [hB]; positivity
  have hG0 : ∀ y, 0 ≤ G y := fun y => by simp only [hG]; positivity
  have hBk : ∀ k ≤ j + 1, ∀ y : E3, ‖iteratedFDeriv ℝ k φ y‖ ≤ B y := fun k hk y => by
    simp only [hB]; exact hbd k hk y
  have hBG : ∀ y, B y ≤ M * G y := fun y => by
    simp only [hB, hG]
    exact mul_le_mul_of_nonneg_left (exp_le_exp_half _ κ c' hκ hc) hM
  have hD : ∀ v : E3, ContDiff ℝ ∞ (fun y : E3 => fderiv ℝ φ y v) := fun v =>
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hV : ∀ v : E3, ‖v‖ ≤ 1 → ∀ k ≤ j, ∀ y : E3,
      ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ φ z v) y‖ ≤ B y := by
    intro v hv k hk y
    refine (iter_dir φ hφ v k y).trans ?_
    calc ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) φ y‖ ≤ 1 * B y :=
          mul_le_mul hv (hBk (k + 1) (by omega) y) (norm_nonneg _) zero_le_one
      _ = B y := one_mul _
  have n1 : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have n2 : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have n3 : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
  have hRi : ‖R⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_le_one_of_one_le₀ hR
  have hD1 := hD (1, (0, 0))
  have hD2 := hD (0, (1, 0))
  have hD3 := hD (0, (0, 1))
  -- the S-weighted term
  have hS_term : ∀ y : E3, ‖iteratedFDeriv ℝ l (fun z => z.1 * fderiv ℝ φ z (1, (0, 0))) y‖ ≤
      S * B y + (l : ℝ) * B y := by
    intro y
    have hfun : (fun z : E3 => z.1 * fderiv ℝ φ z (1, (0, 0))) =
        (fun z => (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ) z *
          fderiv ℝ φ z (1, (0, 0))) := by
      funext z; simp
    have h := norm_iter_mul_clm (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      (fun z => fderiv ℝ φ z (1, (0, 0))) hD1 l y
    have hfy : ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ) y‖ = |y.1| := by simp
    have hfn : ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.norm_fst_le _ _ _
    have hgl := hV _ n1 l hl y
    have hgl1 := hV _ n1 (l - 1) (by omega) y
    have key1 : ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ) y‖ *
        ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ φ z (1, (0, 0))) y‖ ≤ S * B y := by
      rw [hfy]
      by_cases hy : |y.1| ≤ S
      · exact mul_le_mul hy hgl (norm_nonneg _) hS.le
      · rw [support_dS φ S hφS hφ' l y (not_le.mp hy), norm_zero, mul_zero]
        exact mul_nonneg hS.le (hB0 y)
    have key2 : (l : ℝ) * ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ)‖ *
        ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (1, (0, 0))) y‖ ≤ (l : ℝ) * B y := by
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have h1 : ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ)‖ *
          ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (1, (0, 0))) y‖ ≤ 1 * B y :=
        mul_le_mul hfn hgl1 (norm_nonneg _) zero_le_one
      calc (l : ℝ) * ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (1, (0, 0))) y‖
          = (l : ℝ) * (‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) : E3 →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (1, (0, 0))) y‖) := by ring
        _ ≤ (l : ℝ) * (1 * B y) := mul_le_mul_of_nonneg_left h1 hl0
        _ = (l : ℝ) * B y := by ring
    rw [hfun]
    linarith [h, key1, key2]
  -- the eta-weighted term
  obtain ⟨L2, hL2⟩ : ∃ L : E3 →L[ℝ] ℝ,
      L = (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) :=
    ⟨_, rfl⟩
  have hL2y : ∀ y : E3, L2 y = y.2.2 := fun y => by rw [hL2]; rfl
  have hL2n : ‖L2‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
    rw [hL2y, one_mul]
    exact (norm_snd_le y.2).trans (norm_snd_le y)
  have hEtm : ∀ y : E3, ‖iteratedFDeriv ℝ l (fun z => z.2.2 * fderiv ℝ φ z (0, (0, 1))) y‖ ≤
      2 * (1 + c' / κ) * (M * G y) + (l : ℝ) * B y := by
    intro y
    have hfun : (fun z : E3 => z.2.2 * fderiv ℝ φ z (0, (0, 1))) =
        (fun z => L2 z * fderiv ℝ φ z (0, (0, 1))) := by
      funext z; rw [hL2y]
    have h := norm_iter_mul_clm L2 (fun z => fderiv ℝ φ z (0, (0, 1))) hD3 l y
    have hgl := hV _ n3 l hl y
    have hgl1 := hV _ n3 (l - 1) (by omega) y
    have hLy : ‖L2 y‖ = |y.2.2| := by rw [hL2y, Real.norm_eq_abs]
    have k1 : ‖L2 y‖ * ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ φ z (0, (0, 1))) y‖ ≤
        2 * (1 + c' / κ) * (M * G y) := by
      rw [hLy]
      have hdecay := exp_decay_bound y.2.2 κ c' hκ hc
      calc |y.2.2| * ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ φ z (0, (0, 1))) y‖
          ≤ |y.2.2| * B y := mul_le_mul_of_nonneg_left hgl (abs_nonneg _)
        _ = M * (|y.2.2| * Real.exp (-(κ * |y.2.2| / c'))) := by simp only [hB]; ring
        _ ≤ M * (2 * (1 + c' / κ) * Real.exp (-((κ / 2) * |y.2.2| / c'))) :=
          mul_le_mul_of_nonneg_left hdecay hM
        _ = 2 * (1 + c' / κ) * (M * G y) := by simp only [hG]; ring
    have k2 : (l : ℝ) * ‖L2‖ * ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (0, (0, 1))) y‖ ≤
        (l : ℝ) * B y := by
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have h1 : ‖L2‖ * ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (0, (0, 1))) y‖ ≤
          1 * B y := mul_le_mul hL2n hgl1 (norm_nonneg _) zero_le_one
      calc (l : ℝ) * ‖L2‖ * ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (0, (0, 1))) y‖
          = (l : ℝ) * (‖L2‖ * ‖iteratedFDeriv ℝ (l - 1) (fun z => fderiv ℝ φ z (0, (0, 1))) y‖) :=
            by ring
        _ ≤ (l : ℝ) * (1 * B y) := mul_le_mul_of_nonneg_left h1 hl0
        _ = (l : ℝ) * B y := by ring
    rw [hfun]
    linarith [h, k1, k2]
  -- constants at the point m
  have hs1 : 1 ≤ (1 + S) * (1 + c' / κ) := by
    have h0 : 0 ≤ c' / κ := by positivity
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hMG0 : 0 ≤ M * G m := mul_nonneg hM (hG0 m)
  have hAm0 : 0 ≤ (1 + S) * (1 + c' / κ) * (M * G m) := mul_nonneg (by linarith [hs1]) hMG0
  have hMGA : M * G m ≤ (1 + S) * (1 + c' / κ) * (M * G m) :=
    le_mul_of_one_le_left hMG0 hs1
  have hBA : B m ≤ (1 + S) * (1 + c' / κ) * (M * G m) := (hBG m).trans hMGA
  have hSle : S ≤ (1 + S) * (1 + c' / κ) := by nlinarith [hc, hκ, div_pos hc hκ]
  have hSB : S * B m ≤ (1 + S) * (1 + c' / κ) * (M * G m) :=
    calc S * B m ≤ S * (M * G m) := mul_le_mul_of_nonneg_left (hBG m) hS.le
      _ ≤ (1 + S) * (1 + c' / κ) * (M * G m) := mul_le_mul_of_nonneg_right hSle hMG0
  have hlj : (l : ℝ) ≤ j := by exact_mod_cast hl
  have hjAm : 0 ≤ (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)) :=
    mul_nonneg (Nat.cast_nonneg j) hAm0
  have hlB : (l : ℝ) * B m ≤ (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)) :=
    mul_le_mul hlj hBA (hB0 m) (Nat.cast_nonneg j)
  have hE2 : 2 * (1 + c' / κ) * (M * G m) ≤ 2 * ((1 + S) * (1 + c' / κ) * (M * G m)) := by
    have h1 : (1 + c' / κ) ≤ (1 + S) * (1 + c' / κ) := le_mul_of_one_le_left (by positivity) (by linarith)
    have h2 := mul_le_mul_of_nonneg_right h1 hMG0
    nlinarith [h2]
  -- components
  have hcomp_a : ‖iteratedFDeriv ℝ l (fun y => -(fderiv ℝ φ y (0, (0, 1)))) m‖ ≤
      (1 + S) * (1 + c' / κ) * (M * G m) := by
    rw [iter_neg']; exact (hV _ n3 l hl m).trans hBA
  have hcomp_q : ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ φ z (0, (1, 0))) m‖ ≤
      (1 + S) * (1 + c' / κ) * (M * G m) := (hV _ n2 l hl m).trans hBA
  have hcomp_phi : ‖iteratedFDeriv ℝ l φ m‖ ≤ (1 + S) * (1 + c' / κ) * (M * G m) :=
    (hBk l (by omega) m).trans hBA
  have hcomp_S : ‖iteratedFDeriv ℝ l (fun z => z.1 * fderiv ℝ φ z (1, (0, 0))) m‖ ≤
      (1 + S) * (1 + c' / κ) * (M * G m) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)) := by
    have := hS_term m
    linarith [hSB, hlB]
  have hcomp_E : ‖iteratedFDeriv ℝ l (fun z => z.2.2 * fderiv ℝ φ z (0, (0, 1))) m‖ ≤
      2 * ((1 + S) * (1 + c' / κ) * (M * G m)) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)) := by
    have := hEtm m
    linarith [hE2, hlB]
  -- the second component
  have hcd1 : ContDiff ℝ ∞ (fun z : E3 => z.1 * fderiv ℝ φ z (1, (0, 0))) := by fun_prop
  have hcd2 : ContDiff ℝ ∞ (fun z : E3 => z.2.2 * fderiv ℝ φ z (0, (0, 1))) := by fun_prop
  have hcd3 : ContDiff ℝ ∞ (fun z : E3 => 2 * (z.1 * fderiv ℝ φ z (1, (0, 0)))) := by fun_prop
  have hcd4 : ContDiff ℝ ∞ (fun z : E3 => φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0)))) := by
    fun_prop
  have hcd5 : ContDiff ℝ ∞ (fun z : E3 => φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) -
      z.2.2 * fderiv ℝ φ z (0, (0, 1))) := by fun_prop
  have hcd6 : ContDiff ℝ ∞ (fun z : E3 => R⁻¹ * (φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) -
      z.2.2 * fderiv ℝ φ z (0, (0, 1)))) := by fun_prop
  have hcd7 : ContDiff ℝ ∞ (fun z : E3 => fderiv ℝ φ z (0, (1, 0)) + R⁻¹ * (φ z -
      2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) - z.2.2 * fderiv ℝ φ z (0, (0, 1)))) := by fun_prop
  have hX2 : ‖iteratedFDeriv ℝ l (fun z : E3 => 2 * (z.1 * fderiv ℝ φ z (1, (0, 0)))) m‖ ≤
      2 * ((1 + S) * (1 + c' / κ) * (M * G m) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m))) := by
    have h := iter_cmul' 2 (fun z : E3 => z.1 * fderiv ℝ φ z (1, (0, 0))) hcd1 l m
    have e2 : ‖(2 : ℝ)‖ = 2 := by norm_num
    rw [e2] at h
    linarith [h, hcomp_S]
  have hF1 : ‖iteratedFDeriv ℝ l (fun z : E3 => φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0)))) m‖ ≤
      (1 + S) * (1 + c' / κ) * (M * G m) +
        2 * ((1 + S) * (1 + c' / κ) * (M * G m) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m))) := by
    have h := iter_sub' φ (fun z : E3 => 2 * (z.1 * fderiv ℝ φ z (1, (0, 0)))) hφ hcd3 l m
    linarith [h, hX2, hcomp_phi]
  have hF2 : ‖iteratedFDeriv ℝ l (fun z : E3 => φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) -
      z.2.2 * fderiv ℝ φ z (0, (0, 1))) m‖ ≤
      ((1 + S) * (1 + c' / κ) * (M * G m) +
        2 * ((1 + S) * (1 + c' / κ) * (M * G m) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)))) +
      (2 * ((1 + S) * (1 + c' / κ) * (M * G m)) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m))) := by
    have h := iter_sub' (fun z : E3 => φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))))
      (fun z : E3 => z.2.2 * fderiv ℝ φ z (0, (0, 1))) hcd4 hcd2 l m
    linarith [h, hF1, hcomp_E]
  have hF3 : ‖iteratedFDeriv ℝ l (fun z : E3 => R⁻¹ * (φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) -
      z.2.2 * fderiv ℝ φ z (0, (0, 1)))) m‖ ≤ ‖iteratedFDeriv ℝ l (fun z : E3 =>
        φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) - z.2.2 * fderiv ℝ φ z (0, (0, 1))) m‖ := by
    have h := iter_cmul' R⁻¹ (fun z : E3 => φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) -
      z.2.2 * fderiv ℝ φ z (0, (0, 1))) hcd5 l m
    exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hRi)
  have hbb : ‖iteratedFDeriv ℝ l (fun z : E3 => fderiv ℝ φ z (0, (1, 0)) + R⁻¹ * (φ z -
      2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) - z.2.2 * fderiv ℝ φ z (0, (0, 1)))) m‖ ≤
      (1 + S) * (1 + c' / κ) * (M * G m) + (((1 + S) * (1 + c' / κ) * (M * G m) +
        2 * ((1 + S) * (1 + c' / κ) * (M * G m) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)))) +
      (2 * ((1 + S) * (1 + c' / κ) * (M * G m)) + (j : ℝ) * ((1 + S) * (1 + c' / κ) * (M * G m)))) := by
    have h1 := iter_add' (fun z : E3 => fderiv ℝ φ z (0, (1, 0)))
      (fun z : E3 => R⁻¹ * (φ z - 2 * (z.1 * fderiv ℝ φ z (1, (0, 0))) -
        z.2.2 * fderiv ℝ φ z (0, (0, 1)))) hD2 hcd6 l m
    linarith [h1, hF3, hF2, hcomp_q]
  -- the profile decomposition
  have hP : Axi.ringStreamProfile R φ = fun y : E3 =>
      (-(fderiv ℝ φ y (0, (0, 1)))) • Axi.m0 + (fderiv ℝ φ y (0, (1, 0)) + R⁻¹ * (φ y -
        2 * (y.1 * fderiv ℝ φ y (1, (0, 0))) - y.2.2 * fderiv ℝ φ y (0, (0, 1)))) • Axi.m1 := by
    funext y
    simp only [Axi.ringStreamProfile, Axi.dEta, Axi.dS, Axi.dQ, mul_assoc]
  have ha : ContDiff ℝ ∞ (fun y : E3 => -(fderiv ℝ φ y (0, (0, 1)))) := hD3.neg
  have hb : ContDiff ℝ ∞ (fun y : E3 => fderiv ℝ φ y (0, (1, 0)) + R⁻¹ * (φ y -
      2 * (y.1 * fderiv ℝ φ y (1, (0, 0))) - y.2.2 * fderiv ℝ φ y (0, (0, 1)))) := hcd7
  have hmain := iter_vec_add (fun y : E3 => -(fderiv ℝ φ y (0, (0, 1))))
    (fun y : E3 => fderiv ℝ φ y (0, (1, 0)) + R⁻¹ * (φ y -
      2 * (y.1 * fderiv ℝ φ y (1, (0, 0))) - y.2.2 * fderiv ℝ φ y (0, (0, 1)))) ha hb
    Axi.m0 Axi.m1 l m
  beta_reduce at hmain
  have hm0 : ‖Axi.m0‖ = 1 := by simp [Axi.m0]
  have hm1 : ‖Axi.m1‖ = 1 := by simp [Axi.m1]
  rw [hm0, hm1] at hmain
  have hGm : Real.exp (-((κ / 2) * |m.2.2| / c')) = G m := by simp only [hG]
  rw [hP, hGm]
  have eR : 10 * ((j : ℝ) + 1) * (1 + S) * (1 + c' / κ) * M * G m =
      10 * ((j : ℝ) + 1) * ((1 + S) * (1 + c' / κ) * (M * G m)) := by ring
  rw [eR]
  linarith [hmain, hcomp_a, hbb, hjAm, hAm0]

end UnforcedLeray.Short.IIb
