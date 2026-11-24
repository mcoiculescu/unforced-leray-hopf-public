import UnforcedLeray.Short.PartI.Sub.T02_1_2_4

/-!
# Part I, task `PartI:T02/1/2/5`: linear Picard core

Abstract core for `StepDerivative` (source `the November 2 reference manuscript`,
lines 261-288).  For `B` additive in each argument with the product rule and the weighted
estimates, `w = h + B u w + B w u`, `h` with a derivative path, `u` with a derivative path:
`w` has a derivative path.  Picard iteration `w_0 = h`, `w_{m+1} = h + L w_m` (`L x = B u x + B x u`)
in the Bielecki norm; the derivative iterates `w_m'` are Cauchy and `DerivClosed` gives the limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

set_option maxHeartbeats 1000000 in
theorem linearPicardCore {c T : ℝ} [CompleteSpace (MPath c T)] (j : Fin 2)
    (B : MPath c T → MPath c T → MPath c T)
    (hBadd1 : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (hBadd2 : ∀ a b b', B a (b + b') = B a b + B a b')
    (hBprod : ∀ a a' b b', HasDerivPath c T j a a' → HasDerivPath c T j b b' →
      HasDerivPath c T j (B a b) (B a' b + B a b'))
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hWl : ∀ (a b : MPath c T) (lam α β' : ℝ), 0 < lam → 0 ≤ α → 0 ≤ β' →
      (∀ t : Icc (0 : ℝ) T, ‖a t‖ ≤ α * Real.exp (lam * t)) →
      (∀ t : Icc (0 : ℝ) T, ‖b t‖ ≤ β') →
      ∀ t : Icc (0 : ℝ) T, ‖(B a b) t‖ ≤ C₀ / Real.sqrt lam * α * β' * Real.exp (lam * t))
    (hWr : ∀ (a b : MPath c T) (lam α β' : ℝ), 0 < lam → 0 ≤ α → 0 ≤ β' →
      (∀ t : Icc (0 : ℝ) T, ‖a t‖ ≤ β') →
      (∀ t : Icc (0 : ℝ) T, ‖b t‖ ≤ α * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T, ‖(B a b) t‖ ≤ C₀ / Real.sqrt lam * α * β' * Real.exp (lam * t))
    (hC : ∀ (a a' : ℕ → MPath c T) (x d : MPath c T),
      (∀ m, HasDerivPath c T j (a m) (a' m)) → Tendsto a atTop (𝓝 x) →
      Tendsto a' atTop (𝓝 d) → HasDerivPath c T j x d)
    (u u' h h' w : MPath c T) (hu : HasDerivPath c T j u u') (hh : HasDerivPath c T j h h')
    (hw : w = h + (B u w + B w u)) :
    ∃ d : MPath c T, HasDerivPath c T j w d := by
  obtain ⟨L, hL⟩ : ∃ L : MPath c T → MPath c T, ∀ x, L x = B u x + B x u := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : MPath c T → MPath c T, ∀ x, G x = B u' x + B x u' := ⟨_, fun _ => rfl⟩
  have hLadd : ∀ a b, L (a + b) = L a + L b := by
    intro a b; rw [hL, hL, hL, hBadd2, hBadd1]; abel
  have hGadd : ∀ a b, G (a + b) = G a + G b := by
    intro a b; rw [hG, hG, hG, hBadd2, hBadd1]; abel
  have hLsub : ∀ a b, L (a - b) = L a - L b := by
    intro a b
    have := hLadd (a - b) b
    rw [sub_add_cancel] at this
    rw [this]; abel
  have hGsub : ∀ a b, G (a - b) = G a - G b := by
    intro a b
    have := hGadd (a - b) b
    rw [sub_add_cancel] at this
    rw [this]; abel
  have hw' : w = h + L w := by rw [hL]; exact hw
  -- constants
  set R : ℝ := ‖u‖ + 1 with hR
  have hR0 : 0 < R := by have := norm_nonneg u; linarith
  set lam : ℝ := (4 * C₀ * R) ^ 2 + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam0
  have hsq : 4 * C₀ * R ≤ Real.sqrt lam := by
    have h1 : (4 * C₀ * R) ^ 2 ≤ lam := by rw [hlam]; linarith
    calc 4 * C₀ * R = Real.sqrt ((4 * C₀ * R) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt lam := Real.sqrt_le_sqrt h1
  set K : ℝ := C₀ / Real.sqrt lam with hK
  have hK0 : 0 < K := div_pos hC₀ hsl0
  have hKR : 2 * K * R ≤ 1 / 2 := by
    have h1 : K * Real.sqrt lam = C₀ := by rw [hK]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq hK0.le, hR0, hK0]
  have hexp1 : ∀ t : Icc (0 : ℝ) T, 1 ≤ Real.exp (lam * t) := fun t =>
    Real.one_le_exp (mul_nonneg hlam0.le t.2.1)
  have hexpT' : ∀ t : Icc (0 : ℝ) T, Real.exp (lam * t) ≤ Real.exp (lam * T) := fun t =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left t.2.2 hlam0.le)
  have hexp0 : ∀ t : Icc (0 : ℝ) T, 0 < Real.exp (lam * t) := fun t => Real.exp_pos _
  have hRu : ∀ t : Icc (0 : ℝ) T, ‖u t‖ ≤ R := fun t => by
    have := u.norm_coe_le_norm t
    rw [hR]; linarith
  have hu'b : ∀ t : Icc (0 : ℝ) T, ‖u' t‖ ≤ ‖u'‖ := fun t => u'.norm_coe_le_norm t
  -- weighted contraction of `L`
  have hLw : ∀ (x : MPath c T) (α : ℝ), 0 ≤ α → (∀ t : Icc (0 : ℝ) T, ‖x t‖ ≤ α * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T, ‖(L x) t‖ ≤ 1 / 2 * (α * Real.exp (lam * t)) := by
    intro x α hα hx t
    have b1 := hWr u x lam α R hlam0 hα hR0.le hRu hx t
    have b2 := hWl x u lam α R hlam0 hα hR0.le hx hRu t
    have hkey : 2 * K * R * (α * Real.exp (lam * t)) ≤ 1 / 2 * (α * Real.exp (lam * t)) :=
      mul_le_mul_of_nonneg_right hKR (mul_nonneg hα (hexp0 t).le)
    rw [hL]
    calc ‖(B u x + B x u) t‖ = ‖(B u x) t + (B x u) t‖ := rfl
      _ ≤ ‖(B u x) t‖ + ‖(B x u) t‖ := norm_add_le _ _
      _ ≤ K * α * R * Real.exp (lam * t) + K * α * R * Real.exp (lam * t) := add_le_add b1 b2
      _ = 2 * K * R * (α * Real.exp (lam * t)) := by ring
      _ ≤ _ := hkey
  -- weighted bound of the forcing operator `G`
  have hGw : ∀ (x : MPath c T) (α : ℝ), 0 ≤ α → (∀ t : Icc (0 : ℝ) T, ‖x t‖ ≤ α * Real.exp (lam * t)) →
      ∀ t : Icc (0 : ℝ) T, ‖(G x) t‖ ≤ 2 * K * ‖u'‖ * α * Real.exp (lam * t) := by
    intro x α hα hx t
    have b1 := hWr u' x lam α ‖u'‖ hlam0 hα (norm_nonneg _) hu'b hx t
    have b2 := hWl x u' lam α ‖u'‖ hlam0 hα (norm_nonneg _) hx hu'b t
    rw [hG]
    calc ‖(B u' x + B x u') t‖ = ‖(B u' x) t + (B x u') t‖ := rfl
      _ ≤ ‖(B u' x) t‖ + ‖(B x u') t‖ := norm_add_le _ _
      _ ≤ K * α * ‖u'‖ * Real.exp (lam * t) + K * α * ‖u'‖ * Real.exp (lam * t) := add_le_add b1 b2
      _ = _ := by ring
  -- the Picard sequence on pairs
  let step : MPath c T × MPath c T → MPath c T × MPath c T := fun p =>
    (h + L p.1, h' + G p.1 + L p.2)
  let seq : ℕ → MPath c T × MPath c T := fun m => step^[m] (h, h')
  have hseq0 : seq 0 = (h, h') := rfl
  have hseqS : ∀ m, seq (m + 1) = step (seq m) := fun m =>
    Function.iterate_succ_apply' step m (h, h')
  have hseq1 : ∀ m, (seq (m + 1)).1 = h + L (seq m).1 := fun m => by rw [hseqS]
  have hseq2 : ∀ m, (seq (m + 1)).2 = h' + G (seq m).1 + L (seq m).2 := fun m => by rw [hseqS]
  have F1 : ∀ m, HasDerivPath c T j (seq m).1 (seq m).2 := by
    intro m
    induction m with
    | zero => exact hh
    | succ m ih =>
      rw [hseq1, hseq2]
      have := hh.add ((hBprod _ _ _ _ hu ih).add (hBprod _ _ _ _ ih hu))
      have e1 : h + L (seq m).1 = h + (B u (seq m).1 + B (seq m).1 u) := by rw [hL]
      have e2 : h' + G (seq m).1 + L (seq m).2 =
          h' + ((B u' (seq m).1 + B u (seq m).2) + (B (seq m).2 u + B (seq m).1 u')) := by
        rw [hL, hG]; abel
      rw [e1, e2]; exact this
  -- (F2) convergence to `w` in the weighted envelope
  set M0 : ℝ := ‖h - w‖ with hM0
  have hM00 : 0 ≤ M0 := norm_nonneg _
  have hdiff : ∀ v : MPath c T, h + L v - w = L (v - w) := by
    intro v
    rw [hLsub]
    calc h + L v - w = h + L v - (h + L w) := by rw [← hw']
      _ = L v - L w := by abel
  have F2 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T,
      ‖(seq m).1 t - w t‖ ≤ (1 / 2) ^ m * M0 * Real.exp (lam * t) := by
    intro m
    induction m with
    | zero =>
      intro t
      rw [hseq0]
      simp only [pow_zero, one_mul]
      calc ‖h t - w t‖ = ‖(h - w) t‖ := rfl
        _ ≤ M0 := (h - w).norm_coe_le_norm t
        _ = M0 * 1 := (mul_one _).symm
        _ ≤ M0 * Real.exp (lam * t) := mul_le_mul_of_nonneg_left (hexp1 t) hM00
    | succ m ih =>
      intro t
      have hfun : (seq (m + 1)).1 - w = L ((seq m).1 - w) := by rw [hseq1]; exact hdiff _
      have e : (seq (m + 1)).1 t - w t = (L ((seq m).1 - w)) t := by
        have := congrArg (fun f : MPath c T => f t) hfun
        simpa only [ContinuousMap.sub_apply] using this
      have hα : 0 ≤ (1 / 2 : ℝ) ^ m * M0 := by positivity
      have hvu : ∀ t : Icc (0 : ℝ) T,
          ‖((seq m).1 - w) t‖ ≤ (1 / 2) ^ m * M0 * Real.exp (lam * t) := fun t => by
        rw [ContinuousMap.sub_apply]; exact ih t
      have := hLw _ _ hα hvu t
      rw [e]
      calc _ ≤ _ := this
        _ = (1 / 2) ^ (m + 1) * M0 * Real.exp (lam * t) := by ring
  -- bound for the iterates
  set S : ℝ := ‖w‖ + M0 * Real.exp (lam * T) with hS
  have hS0 : 0 ≤ S := add_nonneg (norm_nonneg _) (mul_nonneg hM00 (Real.exp_pos _).le)
  have F3 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T, ‖(seq m).1 t‖ ≤ S * Real.exp (lam * t) := by
    intro m t
    have h1 := F2 m t
    have hp : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc ‖(seq m).1 t‖ = ‖w t + ((seq m).1 t - w t)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w t‖ + ‖(seq m).1 t - w t‖ := norm_add_le _ _
      _ ≤ ‖w‖ + M0 * Real.exp (lam * T) := by
        refine add_le_add (w.norm_coe_le_norm t) ?_
        calc ‖(seq m).1 t - w t‖ ≤ (1 / 2) ^ m * M0 * Real.exp (lam * t) := h1
          _ ≤ 1 * M0 * Real.exp (lam * T) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hp hM00) (hexpT' t)
              (hexp0 t).le (by positivity)
          _ = _ := by ring
      _ = S := hS.symm
      _ = S * 1 := (mul_one _).symm
      _ ≤ S * Real.exp (lam * t) := mul_le_mul_of_nonneg_left (hexp1 t) hS0
  -- derivative iterates: envelope bound
  set E : ℝ := ‖h'‖ + 2 * K * ‖u'‖ * S with hE
  have hE0 : 0 ≤ E := add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0.le) (norm_nonneg _)) hS0)
  set Γ : ℝ := 2 * E with hΓ
  have hΓ0 : 0 ≤ Γ := mul_nonneg (by norm_num) hE0
  have F4 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T, ‖(seq m).2 t‖ ≤ Γ * Real.exp (lam * t) := by
    intro m
    induction m with
    | zero =>
      intro t
      rw [hseq0]
      calc ‖h' t‖ ≤ ‖h'‖ := h'.norm_coe_le_norm t
        _ ≤ Γ := by rw [hΓ, hE]; nlinarith [norm_nonneg h', mul_nonneg (mul_nonneg (mul_nonneg
            (by norm_num : (0:ℝ) ≤ 2) hK0.le) (norm_nonneg u')) hS0]
        _ = Γ * 1 := (mul_one _).symm
        _ ≤ Γ * Real.exp (lam * t) := mul_le_mul_of_nonneg_left (hexp1 t) hΓ0
    | succ m ih =>
      intro t
      rw [hseq2]
      have b1 := hGw _ S hS0 (F3 m) t
      have b2 := hLw _ Γ hΓ0 ih t
      have b0 : ‖h' t‖ ≤ ‖h'‖ * Real.exp (lam * t) :=
        (h'.norm_coe_le_norm t).trans (by
          calc ‖h'‖ = ‖h'‖ * 1 := (mul_one _).symm
            _ ≤ ‖h'‖ * Real.exp (lam * t) := mul_le_mul_of_nonneg_left (hexp1 t) (norm_nonneg _))
      calc ‖(h' + G (seq m).1 + L (seq m).2) t‖
          = ‖h' t + (G (seq m).1) t + (L (seq m).2) t‖ := rfl
        _ ≤ ‖h' t‖ + ‖(G (seq m).1) t‖ + ‖(L (seq m).2) t‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ ‖h'‖ * Real.exp (lam * t) + 2 * K * ‖u'‖ * S * Real.exp (lam * t) +
            1 / 2 * (Γ * Real.exp (lam * t)) := add_le_add (add_le_add b0 b1) b2
        _ = Γ * Real.exp (lam * t) := by rw [hΓ, hE]; ring
  -- differences of the derivative iterates
  set c1 : ℝ := 4 * K * ‖u'‖ * M0 with hc1
  have hc10 : 0 ≤ c1 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0.le) (norm_nonneg _)) hM00
  set D : ℝ := max (2 * Γ) (4 * c1) with hD'
  have hD0 : 0 ≤ D := le_trans (mul_nonneg (by norm_num) hΓ0) (le_max_left _ _)
  have hD1 : 2 * Γ ≤ D := le_max_left _ _
  have hD2 : 4 * c1 ≤ D := le_max_right _ _
  have hdw : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T,
      ‖((seq (m + 1)).1 - (seq m).1) t‖ ≤ (2 * (1 / 2) ^ m * M0) * Real.exp (lam * t) := by
    intro m t
    have h1 := F2 (m + 1) t
    have h2 := F2 m t
    calc ‖((seq (m + 1)).1 - (seq m).1) t‖
        = ‖((seq (m + 1)).1 t - w t) - ((seq m).1 t - w t)‖ := by
          congr 1; simp only [ContinuousMap.sub_apply]; abel
      _ ≤ ‖(seq (m + 1)).1 t - w t‖ + ‖(seq m).1 t - w t‖ := norm_sub_le _ _
      _ ≤ (1 / 2) ^ (m + 1) * M0 * Real.exp (lam * t) + (1 / 2) ^ m * M0 * Real.exp (lam * t) :=
          add_le_add h1 h2
      _ ≤ (2 * (1 / 2) ^ m * M0) * Real.exp (lam * t) := by
          have : (1 / 2 : ℝ) ^ (m + 1) = 1 / 2 * (1 / 2) ^ m := by ring
          rw [this]
          have : 0 ≤ (1 / 2 : ℝ) ^ m * M0 * Real.exp (lam * t) := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hM00) (hexp0 t).le
          nlinarith
  have F5 : ∀ m : ℕ, ∀ t : Icc (0 : ℝ) T,
      ‖((seq (m + 1)).2 - (seq m).2) t‖ ≤ D * (3 / 4) ^ m * Real.exp (lam * t) := by
    intro m
    induction m with
    | zero =>
      intro t
      calc ‖((seq (0 + 1)).2 - (seq 0).2) t‖ = ‖(seq (0 + 1)).2 t - (seq 0).2 t‖ := rfl
        _ ≤ ‖(seq (0 + 1)).2 t‖ + ‖(seq 0).2 t‖ := norm_sub_le _ _
        _ ≤ Γ * Real.exp (lam * t) + Γ * Real.exp (lam * t) := add_le_add (F4 _ t) (F4 _ t)
        _ = 2 * Γ * Real.exp (lam * t) := by ring
        _ ≤ D * (3 / 4) ^ 0 * Real.exp (lam * t) := by
          rw [pow_zero, mul_one]
          exact mul_le_mul_of_nonneg_right hD1 (hexp0 t).le
    | succ m ih =>
      intro t
      have hid : (seq (m + 1 + 1)).2 - (seq (m + 1)).2 =
          G ((seq (m + 1)).1 - (seq m).1) + L ((seq (m + 1)).2 - (seq m).2) := by
        rw [hseq2 (m + 1), hseq2 m, hGsub, hLsub]; abel
      have hα1 : 0 ≤ 2 * (1 / 2 : ℝ) ^ m * M0 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)) hM00
      have hα2 : 0 ≤ D * (3 / 4 : ℝ) ^ m := mul_nonneg hD0 (pow_nonneg (by norm_num) _)
      have g1 := hGw _ _ hα1 (hdw m) t
      have g2 := hLw _ _ hα2 ih t
      have e : ((seq (m + 1 + 1)).2 - (seq (m + 1)).2) t =
          (G ((seq (m + 1)).1 - (seq m).1)) t + (L ((seq (m + 1)).2 - (seq m).2)) t := by
        have := congrArg (fun f : MPath c T => f t) hid
        simpa only [ContinuousMap.add_apply] using this
      have hpow : (1 / 2 : ℝ) ^ m ≤ (3 / 4) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
      have hpow0 : 0 ≤ (3 / 4 : ℝ) ^ m := by positivity
      have he := (hexp0 t).le
      have hsm : 2 * K * ‖u'‖ * (2 * (1 / 2 : ℝ) ^ m * M0) ≤ D / 4 * (3 / 4) ^ m := by
        have h1 : 2 * K * ‖u'‖ * (2 * (1 / 2 : ℝ) ^ m * M0) = c1 * (1 / 2) ^ m := by
          rw [hc1]; ring
        rw [h1]
        calc c1 * (1 / 2 : ℝ) ^ m ≤ c1 * (3 / 4) ^ m := mul_le_mul_of_nonneg_left hpow hc10
          _ ≤ D / 4 * (3 / 4) ^ m := mul_le_mul_of_nonneg_right (by linarith) hpow0
      rw [e]
      calc ‖(G ((seq (m + 1)).1 - (seq m).1)) t + (L ((seq (m + 1)).2 - (seq m).2)) t‖
          ≤ ‖(G ((seq (m + 1)).1 - (seq m).1)) t‖ + ‖(L ((seq (m + 1)).2 - (seq m).2)) t‖ :=
            norm_add_le _ _
        _ ≤ 2 * K * ‖u'‖ * (2 * (1 / 2) ^ m * M0) * Real.exp (lam * t) +
            1 / 2 * (D * (3 / 4) ^ m * Real.exp (lam * t)) := add_le_add g1 g2
        _ ≤ D / 4 * (3 / 4) ^ m * Real.exp (lam * t) +
            1 / 2 * (D * (3 / 4) ^ m * Real.exp (lam * t)) :=
            add_le_add (mul_le_mul_of_nonneg_right hsm he) le_rfl
        _ = D * (3 / 4) ^ (m + 1) * Real.exp (lam * t) := by ring
  -- Cauchy
  have hdist : ∀ m : ℕ, dist (seq m).2 (seq (m + 1)).2 ≤ (D * Real.exp (lam * T)) * (3 / 4) ^ m := by
    intro m
    rw [dist_eq_norm, norm_sub_rev]
    refine (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg hD0 (Real.exp_pos _).le) (pow_nonneg (by norm_num) _))).2 (fun t => ?_)
    calc ‖((seq (m + 1)).2 - (seq m).2) t‖ ≤ D * (3 / 4) ^ m * Real.exp (lam * t) := F5 m t
      _ ≤ D * (3 / 4) ^ m * Real.exp (lam * T) :=
          mul_le_mul_of_nonneg_left (hexpT' t) (mul_nonneg hD0 (pow_nonneg (by norm_num) _))
      _ = (D * Real.exp (lam * T)) * (3 / 4) ^ m := by ring
  have hcau : CauchySeq (fun m => (seq m).2) :=
    cauchySeq_of_le_geometric (3 / 4) (D * Real.exp (lam * T)) (by norm_num) hdist
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcau
  have ht1 : Tendsto (fun m => (seq m).1) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m * (M0 * Real.exp (lam * T))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul_const (M0 * Real.exp (lam * T))
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hlim
    refine (ContinuousMap.norm_le _ (mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hM00 (Real.exp_pos _).le))).2 (fun t => ?_)
    calc ‖((seq m).1 - w) t‖ = ‖(seq m).1 t - w t‖ := rfl
      _ ≤ (1 / 2) ^ m * M0 * Real.exp (lam * t) := F2 m t
      _ ≤ (1 / 2) ^ m * M0 * Real.exp (lam * T) :=
          mul_le_mul_of_nonneg_left (hexpT' t) (mul_nonneg (pow_nonneg (by norm_num) _) hM00)
      _ = (1 / 2) ^ m * (M0 * Real.exp (lam * T)) := by ring
  exact ⟨d, hC (fun m => (seq m).1) (fun m => (seq m).2) w d F1 ht1 hd⟩

end UnforcedLeray.Short.PartI
