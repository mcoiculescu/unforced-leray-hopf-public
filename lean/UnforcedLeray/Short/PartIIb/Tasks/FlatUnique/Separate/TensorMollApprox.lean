import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollTranspose

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIb


/-! ## Support of product kernels -/

theorem tma_kernel_zero (r : ℝ) (ρ₁ : ℝ → ℝ) (ρ₂ : ℝ × ℝ → ℝ)
    (h1 : ∀ t : ℝ, r < |t| → ρ₁ t = 0)
    (h2 : ∀ w : ℝ × ℝ, (r < |w.1| ∨ r < |w.2|) → ρ₂ w = 0)
    (z : Coord) (hz : r < ‖z‖) : ρ₁ z.1 * ρ₂ z.2 = 0 := by
  have e : ‖z‖ = max |z.1| (max |z.2.1| |z.2.2|) := by
    rw [Prod.norm_def, Prod.norm_def]
    simp only [Real.norm_eq_abs]
  rw [e] at hz
  simp only [lt_max_iff] at hz
  rcases hz with h | h | h
  · rw [h1 _ h, zero_mul]
  · rw [h2 z.2 (Or.inl h), mul_zero]
  · rw [h2 z.2 (Or.inr h), mul_zero]

/-! ## One-dimensional and planar normalized bumps -/

def tmaBump1 (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := by linarith }

def tmaBump2 (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ × ℝ) :=
  { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := by linarith }

def tmaρ₁ (r : ℝ) (hr : 0 < r) : ℝ → ℝ := (tmaBump1 r hr).normed volume

def tmaρ₂ (r : ℝ) (hr : 0 < r) : ℝ × ℝ → ℝ := (tmaBump2 r hr).normed volume

theorem tmaρ₁_zero (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : r < |t|) : tmaρ₁ r hr t = 0 := by
  have h0 : (tmaBump1 r hr) t = 0 := by
    apply (tmaBump1 r hr).zero_of_le_dist
    show r ≤ dist t 0
    rw [Real.dist_eq, sub_zero]
    exact ht.le
  show (tmaBump1 r hr) t / _ = 0
  rw [h0, zero_div]

theorem tmaρ₂_zero (r : ℝ) (hr : 0 < r) (w : ℝ × ℝ) (hw : r < |w.1| ∨ r < |w.2|) :
    tmaρ₂ r hr w = 0 := by
  have hd : r ≤ dist w 0 := by
    simp only [Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    rcases hw with h | h
    · exact le_max_of_le_left h.le
    · exact le_max_of_le_right h.le
  have h0 : (tmaBump2 r hr) w = 0 := (tmaBump2 r hr).zero_of_le_dist hd
  show (tmaBump2 r hr) w / _ = 0
  rw [h0, zero_div]

theorem tmaρ₁_nonneg (r : ℝ) (hr : 0 < r) (t : ℝ) : 0 ≤ tmaρ₁ r hr t :=
  (tmaBump1 r hr).nonneg_normed t

theorem tmaρ₂_nonneg (r : ℝ) (hr : 0 < r) (w : ℝ × ℝ) : 0 ≤ tmaρ₂ r hr w :=
  (tmaBump2 r hr).nonneg_normed w

theorem tmaρ₁_cont (r : ℝ) (hr : 0 < r) : Continuous (tmaρ₁ r hr) :=
  (tmaBump1 r hr).continuous_normed

theorem tmaρ₂_cont (r : ℝ) (hr : 0 < r) : Continuous (tmaρ₂ r hr) :=
  (tmaBump2 r hr).continuous_normed

theorem tmaρ₁_cs (r : ℝ) (hr : 0 < r) : HasCompactSupport (tmaρ₁ r hr) :=
  (tmaBump1 r hr).hasCompactSupport_normed

theorem tmaρ₂_cs (r : ℝ) (hr : 0 < r) : HasCompactSupport (tmaρ₂ r hr) :=
  (tmaBump2 r hr).hasCompactSupport_normed

theorem tmaρ₁_int (r : ℝ) (hr : 0 < r) : ∫ t, tmaρ₁ r hr t = 1 :=
  (tmaBump1 r hr).integral_normed

theorem tmaρ₂_int (r : ℝ) (hr : 0 < r) : ∫ w, tmaρ₂ r hr w = 1 :=
  (tmaBump2 r hr).integral_normed

/-- The admissible mollifier pair of radius `r ≤ δ`. -/
theorem tmaKer (δ r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    IsMollKer δ (tmaρ₁ r hr) (tmaρ₂ r hr) where
  smooth₁ := (tmaBump1 r hr).contDiff_normed
  smooth₂ := (tmaBump2 r hr).contDiff_normed
  supp₁ t ht := tmaρ₁_zero r hr t (lt_of_le_of_lt hrδ ht)
  supp₂ w hw := tmaρ₂_zero r hr w
    (hw.imp (fun h => lt_of_le_of_lt hrδ h) (fun h => lt_of_le_of_lt hrδ h))

/-! ## The product kernel on `Coord` -/

def tmaK (r : ℝ) (hr : 0 < r) : Coord → ℝ := fun z => tmaρ₁ r hr z.1 * tmaρ₂ r hr z.2

theorem tmaK_zero (r : ℝ) (hr : 0 < r) (z : Coord) (hz : r < ‖z‖) : tmaK r hr z = 0 :=
  tma_kernel_zero r (tmaρ₁ r hr) (tmaρ₂ r hr) (fun t ht => tmaρ₁_zero r hr t ht)
    (fun w hw => tmaρ₂_zero r hr w hw) z hz

theorem tmaK_norm (r : ℝ) (hr : 0 < r) (z : Coord) (hz : tmaK r hr z ≠ 0) : ‖z‖ ≤ r := by
  by_contra h
  exact hz (tmaK_zero r hr z (not_le.1 h))

theorem tmaK_cont (r : ℝ) (hr : 0 < r) : Continuous (tmaK r hr) :=
  ((tmaρ₁_cont r hr).comp continuous_fst).mul ((tmaρ₂_cont r hr).comp continuous_snd)

theorem tmaK_cs (r : ℝ) (hr : 0 < r) : HasCompactSupport (tmaK r hr) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Coord) r) (fun z hz =>
    tmaK_zero r hr z (not_le.1 (fun h => hz (mem_closedBall_zero_iff.2 h))))

theorem tmaK_nonneg (r : ℝ) (hr : 0 < r) (z : Coord) : 0 ≤ tmaK r hr z :=
  mul_nonneg (tmaρ₁_nonneg r hr _) (tmaρ₂_nonneg r hr _)

theorem tmaK_int (r : ℝ) (hr : 0 < r) : ∫ z : Coord, tmaK r hr z = 1 := by
  unfold tmaK
  rw [Measure.volume_eq_prod, integral_prod_mul (tmaρ₁ r hr) (tmaρ₂ r hr), tmaρ₁_int, tmaρ₂_int,
    one_mul]

/-! ## Radii -/

def tmaE (δ : ℝ) (n : ℕ) : ℝ := δ / ((n : ℝ) + 2)

theorem tmaE_pos (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : 0 < tmaE δ n :=
  div_pos hδ (by positivity)

theorem tmaE_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : tmaE δ n ≤ δ := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact div_le_self hδ.le (by linarith)

theorem tmaE_small (δ : ℝ) (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → tmaE δ n < η := by
  obtain ⟨N, hN⟩ := exists_nat_gt (δ / η)
  refine ⟨N, fun n hn => ?_⟩
  have hN' : δ < (N : ℝ) * η := (div_lt_iff₀ hη).1 hN
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  unfold tmaE
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-! ## Translation invariance on `Coord` -/

theorem tma_int_sub (k : Coord → ℝ) (hk : Integrable k) (y : Coord) :
    Integrable (fun x : Coord => k (x - y)) := by
  rw [Measure.volume_eq_prod] at hk ⊢
  exact hk.comp_sub_right y

theorem tma_sub_right (k : Coord → ℝ) (y : Coord) :
    ∫ x : Coord, k (x - y) = ∫ x : Coord, k x := by
  rw [Measure.volume_eq_prod]
  exact integral_sub_right_eq_self _ _

/-! ## The averaged function -/

def tmaG (g : Coord → ℝ) (k : Coord → ℝ) (y : Coord) : ℝ := ∫ x : Coord, g x * k (x - y)

theorem tma_int_mul {g φ : Coord → ℝ} {C : ℝ} (hgc : Continuous g) (hC : ∀ x, ‖g x‖ ≤ C)
    (hφc : Continuous φ) (hφ : Integrable φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    Integrable (fun x => g x * φ x) := by
  refine Integrable.mono' (hφ.const_mul C) (hgc.mul hφc).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  calc ‖g x * φ x‖ = ‖g x‖ * φ x := by rw [norm_mul, Real.norm_of_nonneg (hφ0 x)]
    _ ≤ C * φ x := mul_le_mul_of_nonneg_right (hC x) (hφ0 x)

theorem tma_G_bound {g k : Coord → ℝ} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hk0 : ∀ z, 0 ≤ k z)
    (hki : Integrable k) (hk1 : ∫ z, k z = 1) (y : Coord) : |tmaG g k y| ≤ C := by
  have hi : Integrable (fun x : Coord => k (x - y)) := tma_int_sub k hki y
  have hb : ∫ x : Coord, k (x - y) = 1 := by
    rw [tma_sub_right k y]; exact hk1
  have hpt : ∀ x : Coord, ‖g x * k (x - y)‖ ≤ C * k (x - y) := fun x => by
    rw [norm_mul, Real.norm_of_nonneg (hk0 _)]
    exact mul_le_mul_of_nonneg_right (hC x) (hk0 _)
  have hle := norm_integral_le_of_norm_le (hi.const_mul C) (ae_of_all _ hpt)
  rw [integral_const_mul, hb, mul_one] at hle
  unfold tmaG
  rw [← Real.norm_eq_abs]
  exact hle

/-- If `tmaG g K y ≠ 0` then `y` lies in the compact set `tsupport g - closedBall 0 r`. -/
theorem tma_G_supp {g : Coord → ℝ} {δ r : ℝ} (hr : 0 < r) (hrδ : r ≤ δ) (y : Coord)
    (hG : tmaG g (tmaK r hr) y ≠ 0) :
    y ∈ (fun p : Coord × Coord => p.1 - p.2) '' (tsupport g ×ˢ Metric.closedBall (0 : Coord) δ) := by
  by_contra hy
  apply hG
  have hz : ∀ x : Coord, g x * tmaK r hr (x - y) = 0 := by
    intro x
    by_cases hx : x ∈ tsupport g
    · by_cases hk : tmaK r hr (x - y) = 0
      · rw [hk, mul_zero]
      · exfalso
        have hn : ‖x - y‖ ≤ r := tmaK_norm r hr _ hk
        exact hy ⟨(x, x - y), Set.mk_mem_prod hx (mem_closedBall_zero_iff.2 (hn.trans hrδ)),
          sub_sub_cancel x y⟩
    · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hgx, zero_mul]
  unfold tmaG
  simp only [hz, integral_zero]

/-! ## Pointwise convergence of the averages -/

theorem tma_pt (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hrlim : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → r n < η)
    {g : Coord → ℝ} {C : ℝ} (hgc : Continuous g) (hC : ∀ x, ‖g x‖ ≤ C) (y : Coord) :
    Tendsto (fun n => tmaG g (tmaK (r n) (hr n)) y) atTop (𝓝 (g y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hηg⟩ := Metric.continuousAt_iff.1 (hgc.continuousAt (x := y)) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hrlim η hη
  refine ⟨N, fun n hn => ?_⟩
  have hki : Integrable (tmaK (r n) (hr n)) :=
    (tmaK_cont _ _).integrable_of_hasCompactSupport (tmaK_cs _ _)
  have hi : Integrable (fun x : Coord => tmaK (r n) (hr n) (x - y)) := tma_int_sub _ hki y
  have hb : ∫ x : Coord, tmaK (r n) (hr n) (x - y) = 1 := by
    rw [tma_sub_right (tmaK (r n) (hr n)) y]; exact tmaK_int _ _
  have hc : Continuous (fun x : Coord => tmaK (r n) (hr n) (x - y)) :=
    (tmaK_cont _ _).comp (continuous_id.sub continuous_const)
  have hI1 : Integrable (fun x : Coord => g x * tmaK (r n) (hr n) (x - y)) :=
    tma_int_mul hgc hC hc hi (fun x => tmaK_nonneg _ _ _)
  have hI2 : Integrable (fun x : Coord => g y * tmaK (r n) (hr n) (x - y)) :=
    hi.const_mul (g y)
  have hint1 : ∫ x : Coord, g y * tmaK (r n) (hr n) (x - y) = g y := by
    rw [integral_const_mul, hb, mul_one]
  have hsub : ∫ x : Coord, (g x - g y) * tmaK (r n) (hr n) (x - y)
      = (∫ x : Coord, g x * tmaK (r n) (hr n) (x - y))
        - ∫ x : Coord, g y * tmaK (r n) (hr n) (x - y) := by
    rw [← integral_sub hI1 hI2]
    congr 1
    funext x
    ring
  have hD : tmaG g (tmaK (r n) (hr n)) y - g y
      = ∫ x : Coord, (g x - g y) * tmaK (r n) (hr n) (x - y) := by
    unfold tmaG
    rw [hsub, hint1]
  have hpt : ∀ x : Coord, ‖(g x - g y) * tmaK (r n) (hr n) (x - y)‖
      ≤ (ε / 2) * tmaK (r n) (hr n) (x - y) := by
    intro x
    by_cases hk : tmaK (r n) (hr n) (x - y) = 0
    · simp [hk]
    · have hnr : ‖x - y‖ ≤ r n := tmaK_norm _ _ _ hk
      have hd : dist x y < η := by
        rw [dist_eq_norm]
        exact lt_of_le_of_lt hnr (hN n hn)
      have hgd := hηg hd
      rw [Real.dist_eq] at hgd
      rw [norm_mul, Real.norm_of_nonneg (tmaK_nonneg _ _ _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hgd.le (tmaK_nonneg _ _ _)
  have hbd := norm_integral_le_of_norm_le (hi.const_mul (ε / 2)) (ae_of_all _ hpt)
  rw [integral_const_mul, hb, mul_one] at hbd
  rw [Real.dist_eq, hD, ← Real.norm_eq_abs]
  linarith

/-! ## Measurability -/

theorem tma_G_meas {g : Coord → ℝ} (hgc : Continuous g) {k : Coord → ℝ} (hkc : Continuous k) :
    StronglyMeasurable (fun y => tmaG g k y) := by
  have hcont : Continuous (fun p : Coord × Coord => g p.2 * k (p.2 - p.1)) :=
    (hgc.comp continuous_snd).mul (hkc.comp (continuous_snd.sub continuous_fst))
  exact StronglyMeasurable.integral_prod_right' (hcont.stronglyMeasurable)

/-! ## Dominated convergence for the averages -/

theorem tmaKey (δ : ℝ) (hδ : 0 < δ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrδ : ∀ n, r n ≤ δ)
    (hrlim : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → r n < η)
    (h : Coord → ℂ) (hh : LocallyIntegrable h volume)
    (hvan : ∀ n (y : Coord), 2 * δ < y.1 → mollG (tmaρ₁ (r n) (hr n)) (tmaρ₂ (r n) (hr n)) h y = 0)
    (g : Coord → ℝ) (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hgU : ∀ x ∈ tsupport g, 2 * δ < x.1) :
    ∫ x : Coord, ((g x : ℝ) : ℂ) * h x = 0 := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  set Lset : Set Coord := (fun p : Coord × Coord => p.1 - p.2) ''
    (tsupport g ×ˢ Metric.closedBall (0 : Coord) δ) with hLset
  have hLc : IsCompact Lset :=
    (hgs.isCompact.prod (isCompact_closedBall (0 : Coord) δ)).image
      (continuous_fst.sub continuous_snd)
  have hBint : Integrable (fun y : Coord => C * Lset.indicator (fun y => ‖h y‖) y) :=
    (IntegrableOn.integrable_indicator ((hh.integrableOn_isCompact hLc).norm) hLc.measurableSet).const_mul C
  have hbd : ∀ n (y : Coord), ‖((tmaG g (tmaK (r n) (hr n)) y : ℝ) : ℂ) * h y‖
      ≤ C * Lset.indicator (fun y => ‖h y‖) y := by
    intro n y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hy : y ∈ Lset
    · rw [Set.indicator_of_mem hy]
      exact mul_le_mul_of_nonneg_right
        (tma_G_bound hC (tmaK_nonneg _ _) (((tmaK_cont _ _).integrable_of_hasCompactSupport
          (tmaK_cs _ _))) (tmaK_int _ _) y) (norm_nonneg _)
    · have h0 : tmaG g (tmaK (r n) (hr n)) y = 0 := by
        by_contra hG
        exact hy (tma_G_supp (hr n) (hrδ n) y hG)
      rw [Set.indicator_of_notMem hy, h0]
      simp
  have hF : ∀ n, AEStronglyMeasurable
      (fun y : Coord => ((tmaG g (tmaK (r n) (hr n)) y : ℝ) : ℂ) * h y) volume := fun n =>
    ((Complex.continuous_ofReal.comp_stronglyMeasurable
      (tma_G_meas hgc (tmaK_cont _ _))).aestronglyMeasurable).mul hh.aestronglyMeasurable
  have hdom := tendsto_integral_of_dominated_convergence
    (fun y : Coord => C * Lset.indicator (fun y => ‖h y‖) y) hF hBint
    (fun n => ae_of_all _ (hbd n))
    (ae_of_all _ fun y => ((Complex.continuous_ofReal.tendsto (g y)).comp
      (tma_pt r hr hrlim hgc hC y)).mul_const (h y))
  have hzero : ∀ n, ∫ y : Coord, ((tmaG g (tmaK (r n) (hr n)) y : ℝ) : ℂ) * h y = 0 := by
    intro n
    have hMT := mollTranspose h (tmaρ₁ (r n) (hr n)) (tmaρ₂ (r n) (hr n)) g hh
      (tmaρ₁_cont _ _) (tmaρ₁_cs _ _) (tmaρ₂_cont _ _) (tmaρ₂_cs _ _) hgc hgs
    have hL : ∫ x : Coord, ((g x : ℝ) : ℂ) *
        mollG (tmaρ₁ (r n) (hr n)) (tmaρ₂ (r n) (hr n)) h x = 0 := by
      have hpt : ∀ x : Coord, ((g x : ℝ) : ℂ) *
          mollG (tmaρ₁ (r n) (hr n)) (tmaρ₂ (r n) (hr n)) h x = 0 := by
        intro x
        by_cases hx : 2 * δ < x.1
        · rw [hvan n x hx, mul_zero]
        · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hgU x hm))
          rw [hgx]
          simp
      simp only [hpt, integral_zero]
    rw [hL] at hMT
    exact hMT.symm
  have hlim0 : Tendsto (fun n => ∫ y : Coord, ((tmaG g (tmaK (r n) (hr n)) y : ℝ) : ℂ) * h y)
      atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdom hlim0

/-! ## The tensor mollification approximation -/

theorem tensorMollApprox : UnforcedLeray.Short.IIb.TensorMollApprox := by
  intro h δ hδ hh hK
  have hU : IsOpen {x : Coord | 2 * δ < x.1} := isOpen_lt continuous_const continuous_fst
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hh.locallyIntegrableOn _) ?_
  intro g hgsm hgs hgU
  have hgc : Continuous g := hgsm.continuous
  have e : ∀ x, g x • h x = ((g x : ℝ) : ℂ) * h x := fun x => Complex.real_smul
  simp only [e]
  exact tmaKey δ hδ (fun n => tmaE δ n) (fun n => tmaE_pos δ hδ n) (fun n => tmaE_le δ hδ n)
    (fun η hη => tmaE_small δ hδ hη) h hh
    (fun n y hy => hK _ _ y (tmaKer δ (tmaE δ n) (tmaE_pos δ hδ n) (tmaE_le δ hδ n)) hy)
    g hgc hgs (fun x hx => hgU hx)

end UnforcedLeray.Short.IIb
