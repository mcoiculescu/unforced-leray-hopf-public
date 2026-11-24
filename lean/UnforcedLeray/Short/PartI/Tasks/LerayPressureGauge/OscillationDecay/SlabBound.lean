import UnforcedLeray.Short.PartI.Sub.T02_2_4
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Part I, task `PartI:T02/2/4/5`: the slab maximum principle `SlabBound`

Source of record: `the November 2 reference manuscript`, line 447 (the decaying
pressure gauge), through the target `SlabBound` (`Short/PartI/Sub/T02_2_4.lean`, line 299).

Proof. Put `m = (a + b) / 2` and `G z = w z ^ 2 + μ (z.2 - m) ^ 2`. On the slab
`a ≤ η ≤ b` the Laplacian of `G` is `2 (∂_q w)² + 2 (∂_η w)² + 2 w Δw + 2 μ`, which is positive
because `|w Δw| < μ`. The function `G` is continuous and `c`-periodic in `q`, so its maximum over
the compact cell `[-c/2, c/2] × [a, b]` is its maximum over the whole slab (periodic reduction).
If the maximum point lies on a boundary line, `G ≤ K + μ (b - a)²/4` there. If it lies in the
open slab, both slice functions `q ↦ G (q, p.2)` and `η ↦ G (p.1, η)` have a local maximum at
`p`, so their second derivatives are `≤ 0` (second derivative test), which contradicts the
positivity of `ΔG`. Finally `w² ≤ G ≤ K + μ (b - a)²/4`, since `μ (z.2 - m)² ≥ 0`.

Helpers are prefixed `sb_`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- A `c`-periodic function can be read with `q` in `[-c/2, c/2]`. -/
theorem sb_reduce {f : ℝ × ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hper : Cyl.IsPeriodic c f) (z : ℝ × ℝ) :
    ∃ q : ℝ, -c / 2 ≤ q ∧ q ≤ c / 2 ∧ f (q, z.2) = f z := by
  have hg : Function.Periodic (fun x : ℝ => f (x, z.2)) c := fun x => hper (x, z.2)
  obtain ⟨n, h1, h2⟩ : ∃ n : ℤ, (n : ℝ) ≤ (z.1 + c / 2) / c ∧ (z.1 + c / 2) / c < (n : ℝ) + 1 :=
    ⟨⌊(z.1 + c / 2) / c⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
  rw [le_div_iff₀ hc] at h1
  rw [div_lt_iff₀ hc] at h2
  refine ⟨z.1 - n * c, by linarith, by linarith, ?_⟩
  have key : (fun x : ℝ => f (x, z.2)) (z.1 - n * c) = (fun x : ℝ => f (x, z.2)) z.1 :=
    hg.sub_int_mul_eq _
  exact key

/-- Second-derivative test (maximum version): a local maximum has nonpositive second derivative. -/
theorem sb_second_nonpos {g : ℝ → ℝ} {x0 : ℝ} (hg : ContinuousAt g x0) (hmax : IsLocalMax g x0) :
    deriv (deriv g) x0 ≤ 0 := by
  by_contra hneg
  push_neg at hneg
  have hd : deriv g x0 = 0 := hmax.deriv_eq_zero
  have hlmin : IsLocalMin g x0 := isLocalMin_of_deriv_deriv_pos hneg hd hg
  have hmin' : ∀ᶠ q in nhds x0, g x0 ≤ g q := hlmin
  have hmax' : ∀ᶠ q in nhds x0, g q ≤ g x0 := hmax
  have hev : g =ᶠ[nhds x0] fun _ => g x0 := by
    filter_upwards [hmin', hmax'] with q h1 h2
    exact le_antisymm h2 h1
  have h3 : deriv (deriv g) x0 = 0 := by
    rw [hev.deriv.deriv_eq]
    simp [deriv_const']
  linarith

/-- The second derivative of `f ^ 2 + k` for `C²` functions `f`, `k` on the line. -/
theorem sb_dd_add {f k : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hk : ContDiff ℝ 2 k) (x : ℝ) :
    deriv (deriv (fun y => f y ^ 2 + k y)) x
      = 2 * deriv f x ^ 2 + 2 * f x * deriv (deriv f) x + deriv (deriv k) x := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hk1 : Differentiable ℝ k := hk.differentiable (by norm_num)
  have hdf : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hdk : Differentiable ℝ (deriv k) := hk.differentiable_deriv_two
  have h1 : deriv (fun y => f y ^ 2 + k y) = fun y => 2 * f y * deriv f y + deriv k y := by
    funext y
    have hd : HasDerivAt (fun y => f y ^ 2 + k y) (2 * f y * deriv f y + deriv k y) y := by
      have h : HasDerivAt (fun y => f y ^ 2 + k y)
          (((2 : ℕ) : ℝ) * f y ^ (2 - 1) * deriv f y + deriv k y) y :=
        ((hf1 y).hasDerivAt.pow 2).add (hk1 y).hasDerivAt
      refine h.congr_deriv ?_
      norm_num
    exact hd.deriv
  rw [h1]
  have h2 : ∀ y, HasDerivAt (fun y => 2 * f y * deriv f y + deriv k y)
      (2 * deriv f y * deriv f y + 2 * f y * deriv (deriv f) y + deriv (deriv k) y) y := by
    intro y
    have ha : HasDerivAt (fun y => 2 * f y * deriv f y)
        (2 * deriv f y * deriv f y + 2 * f y * deriv (deriv f) y) y :=
      ((hf1 y).hasDerivAt.const_mul 2).mul (hdf y).hasDerivAt
    exact ha.add (hdk y).hasDerivAt
  rw [(h2 x).deriv]
  ring

/-- The second derivative of `μ (y - m) ^ 2`. -/
theorem sb_dd_quad (μ m x : ℝ) :
    deriv (deriv (fun y : ℝ => μ * (y - m) ^ 2)) x = 2 * μ := by
  have h1 : deriv (fun y : ℝ => μ * (y - m) ^ 2) = fun y => μ * (2 * (y - m)) := by
    funext y
    have hd : HasDerivAt (fun y : ℝ => μ * (y - m) ^ 2) (μ * (2 * (y - m))) y := by
      have h : HasDerivAt (fun y : ℝ => μ * (y - m) ^ 2)
          (μ * (((2 : ℕ) : ℝ) * (y - m) ^ (2 - 1) * 1)) y :=
        (((hasDerivAt_id' y).sub_const m).pow 2).const_mul μ
      refine h.congr_deriv ?_
      norm_num
    exact hd.deriv
  have h2 : HasDerivAt (fun y : ℝ => μ * (2 * (y - m))) (μ * (2 * 1)) x :=
    (((hasDerivAt_id' x).sub_const m).const_mul 2).const_mul μ
  rw [h1, h2.deriv]
  ring

/-- **Slab maximum principle** (target `SlabBound`, source line 447). -/
theorem slabBound : SlabBound := by
  intro c w hc hw hper a b K μ hab hμ hA hB z hz1 hz2
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a + b) / 2 := ⟨_, rfl⟩
  have hwc : Continuous w := hw.continuous
  have hgc : Continuous (fun y : ℝ × ℝ => w y ^ 2 + μ * (y.2 - m) ^ 2) :=
    (hwc.pow 2).add (continuous_const.mul ((continuous_snd.sub continuous_const).pow 2))
  have hμ0 : 0 ≤ μ := by
    have h1 := hμ z hz1 hz2
    have h2 : 0 ≤ |w z * Train.lapS w z| := abs_nonneg _
    linarith
  -- The maximum of `G` over the compact cell `[-c/2, c/2] × [a, b]`.
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hKne : ((-c / 2, a) : ℝ × ℝ) ∈ (Icc (-c / 2) (c / 2) ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨le_refl _, by show -c / 2 ≤ c / 2; linarith⟩,
      Set.mem_Icc.mpr ⟨le_refl a, hab⟩⟩
  obtain ⟨p, hpK, hpmax⟩ := hK.exists_isMaxOn ⟨_, hKne⟩ hgc.continuousOn
  obtain ⟨hpK1, hpK2⟩ := Set.mem_prod.mp hpK
  obtain ⟨hp2a, hp2b⟩ := Set.mem_Icc.mp hpK2
  -- `G` is maximal over the whole slab: periodicity moves a point into the cell.
  have hmaxall : ∀ y : ℝ × ℝ, a ≤ y.2 → y.2 ≤ b →
      w y ^ 2 + μ * (y.2 - m) ^ 2 ≤ w p ^ 2 + μ * (p.2 - m) ^ 2 := by
    intro y hy1 hy2
    obtain ⟨q, hq1, hq2, hwq⟩ := sb_reduce hc hper y
    have hmem : ((q, y.2) : ℝ × ℝ) ∈ (Icc (-c / 2) (c / 2) ×ˢ Icc a b : Set (ℝ × ℝ)) :=
      Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hq1, hq2⟩, Set.mem_Icc.mpr ⟨hy1, hy2⟩⟩
    have h : w (q, y.2) ^ 2 + μ * (y.2 - m) ^ 2 ≤ w p ^ 2 + μ * (p.2 - m) ^ 2 :=
      isMaxOn_iff.mp hpmax (q, y.2) hmem
    rw [hwq] at h
    exact h
  have hMain : w p ^ 2 + μ * (p.2 - m) ^ 2 ≤ K + μ * (b - a) ^ 2 / 4 := by
    rcases eq_or_lt_of_le hp2a with h1 | h1
    · -- `p` lies on the lower boundary line.
      have hwp : w p ^ 2 ≤ K := by
        have h := hA p.1
        rw [h1] at h
        exact h
      have hsq : μ * (p.2 - m) ^ 2 = μ * (b - a) ^ 2 / 4 := by
        rw [← h1, hm]
        ring
      linarith
    · rcases eq_or_lt_of_le hp2b with h2 | h2
      · -- `p` lies on the upper boundary line.
        have hwp : w p ^ 2 ≤ K := by
          have h := hB p.1
          rw [← h2] at h
          exact h
        have hsq : μ * (p.2 - m) ^ 2 = μ * (b - a) ^ 2 / 4 := by
          rw [h2, hm]
          ring
        linarith
      · exfalso
        -- `p` is an interior maximum: both slice maxima and `ΔG > 0` contradict each other.
        obtain ⟨hfA, hfB⟩ : ContDiff ℝ 2 (fun q : ℝ => w (q, p.2)) ∧
            ContDiff ℝ 2 (fun η : ℝ => w (p.1, η)) :=
          ⟨hw.comp (contDiff_id.prodMk contDiff_const),
            hw.comp (contDiff_const.prodMk contDiff_id)⟩
        have hkA : ContDiff ℝ 2 (fun _ : ℝ => μ * (p.2 - m) ^ 2) := contDiff_const
        have hkB : ContDiff ℝ 2 (fun η : ℝ => μ * (η - m) ^ 2) := by fun_prop
        have hcA : Continuous (fun q : ℝ => w (q, p.2) ^ 2 + μ * (p.2 - m) ^ 2) :=
          (hfA.continuous.pow 2).add continuous_const
        have hcB : Continuous (fun η : ℝ => w (p.1, η) ^ 2 + μ * (η - m) ^ 2) :=
          (hfB.continuous.pow 2).add hkB.continuous
        have hAmax : IsLocalMax (fun q : ℝ => w (q, p.2) ^ 2 + μ * (p.2 - m) ^ 2) p.1 :=
          Filter.Eventually.of_forall (fun q => hmaxall (q, p.2) hp2a hp2b)
        have hBmax : IsLocalMax (fun η : ℝ => w (p.1, η) ^ 2 + μ * (η - m) ^ 2) p.2 :=
          Filter.mem_of_superset (Ioo_mem_nhds h1 h2)
            (fun η hη => hmaxall (p.1, η) hη.1.le hη.2.le)
        have hq := sb_second_nonpos hcA.continuousAt hAmax
        have hη := sb_second_nonpos hcB.continuousAt hBmax
        have dA : deriv (deriv (fun q : ℝ => w (q, p.2) ^ 2 + μ * (p.2 - m) ^ 2)) p.1
            = 2 * Cyl.partialQ w p ^ 2 + 2 * w p * Cyl.partialQ (Cyl.partialQ w) p := by
          have h1' := sb_dd_add hfA hkA p.1
          have hk0 : deriv (deriv (fun _ : ℝ => μ * (p.2 - m) ^ 2)) p.1 = 0 := by simp
          rw [hk0, add_zero] at h1'
          exact h1'
        have dB : deriv (deriv (fun η : ℝ => w (p.1, η) ^ 2 + μ * (η - m) ^ 2)) p.2
            = 2 * Cyl.partialEta w p ^ 2 + 2 * w p * Cyl.partialEta (Cyl.partialEta w) p
              + 2 * μ := by
          have h1' := sb_dd_add hfB hkB p.2
          rw [sb_dd_quad μ m p.2] at h1'
          exact h1'
        have hlap : Train.lapS w p = Cyl.partialQ (Cyl.partialQ w) p
            + Cyl.partialEta (Cyl.partialEta w) p := rfl
        have hsum := add_nonpos hq hη
        rw [dA, dB] at hsum
        have habs := hμ p hp2a hp2b
        rw [abs_lt] at habs
        have hexp : 2 * Cyl.partialQ w p ^ 2 + 2 * w p * Cyl.partialQ (Cyl.partialQ w) p
            + (2 * Cyl.partialEta w p ^ 2 + 2 * w p * Cyl.partialEta (Cyl.partialEta w) p
              + 2 * μ)
            = 2 * Cyl.partialQ w p ^ 2 + 2 * Cyl.partialEta w p ^ 2
              + 2 * (w p * Train.lapS w p) + 2 * μ := by
          rw [hlap]
          ring
        nlinarith [sq_nonneg (Cyl.partialQ w p), sq_nonneg (Cyl.partialEta w p), habs.1,
          hsum, hexp]
  have hfinal := (hmaxall z hz1 hz2).trans hMain
  have hnn : 0 ≤ μ * (z.2 - m) ^ 2 := mul_nonneg hμ0 (sq_nonneg _)
  linarith

end UnforcedLeray.Short.PartI
