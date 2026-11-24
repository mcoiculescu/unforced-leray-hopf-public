import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# `PartIII-b:C/asrc/ra/5/2/4` : the induction `GaussExpStep` for `e^{-q}`

Source 4963-4968.  On the open slab `{p | 0 < p.1}` the Gaussian `E = exp(-q)` satisfies
`D E = E • (-D q)` (`HasFDerivAt.exp`).  Strong induction on the order `m`: the derivative
of order `m+1` is `D^m (E • (-D q))`, which the bilinear Leibniz bound
(`norm_iteratedFDerivWithin_smul_le`) splits into `D^i E` (IH, `i ≤ m`) times
`D^{m-i+1} q` (`GaussQBound`, `O(1+|x|²)`).  Each term is `≤ C_m (1+|x|²)^{m+1} e^{-q}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Set

/-- The open slab `{p | 0 < p.1}` on which the age factor is smooth and positive. -/
def l4Slab : Set (ℝ × (ℝ × ℝ)) := (Prod.fst : ℝ × (ℝ × ℝ) → ℝ) ⁻¹' Ioi (0 : ℝ)

theorem l4Slab_isOpen : IsOpen l4Slab := isOpen_Ioi.preimage continuous_fst

theorem l4Slab_uniq : UniqueDiffOn ℝ l4Slab := l4Slab_isOpen.uniqueDiffOn

theorem l4_sq2_nonneg (x : ℝ × ℝ) : 0 ≤ sq2 x := by
  unfold sq2
  positivity

theorem l4Q_cdOn (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (gaussQ κ ν) l4Slab := by
  have hf : ContDiff ℝ n (fun p : ℝ × (ℝ × ℝ) => sq2 p.2) := by
    unfold sq2
    fun_prop
  have hc : ContDiff ℝ n (fun p : ℝ × (ℝ × ℝ) => κ * ageA ν p.1) := by
    unfold ageA
    fun_prop
  have hg : ContDiffOn ℝ n (fun p : ℝ × (ℝ × ℝ) => (κ * ageA ν p.1)⁻¹) l4Slab := by
    refine hc.contDiffOn.inv ?_
    intro p hp
    have hp' : (0 : ℝ) < p.1 := hp
    have : 0 < ageA ν p.1 := by
      unfold ageA
      nlinarith [mul_pos hν hp']
    exact (mul_pos hκ this).ne'
  unfold gaussQ
  exact hf.contDiffOn.mul hg

theorem l4E_cdOn (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) l4Slab :=
  Real.contDiff_exp.comp_contDiffOn (l4Q_cdOn κ ν hκ hν n).neg

theorem l4Q_hasFDerivAt (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) {p : ℝ × (ℝ × ℝ)}
    (hp : p ∈ l4Slab) :
    HasFDerivAt (fun q : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν q)))
      (Real.exp (-(gaussQ κ ν p)) • -(fderiv ℝ (gaussQ κ ν) p)) p := by
  have hd : DifferentiableAt ℝ (gaussQ κ ν) p :=
    ((l4Q_cdOn κ ν hκ hν 1).differentiableOn one_ne_zero).differentiableAt
      (l4Slab_isOpen.mem_nhds hp)
  exact (hd.hasFDerivAt.neg).exp

theorem l4E_fderivWithin (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) {p : ℝ × (ℝ × ℝ)}
    (hp : p ∈ l4Slab) :
    fderivWithin ℝ (fun q : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν q))) l4Slab p =
      Real.exp (-(gaussQ κ ν p)) • -(fderivWithin ℝ (gaussQ κ ν) l4Slab p) := by
  rw [fderivWithin_of_isOpen l4Slab_isOpen hp, (l4Q_hasFDerivAt κ ν hκ hν hp).fderiv,
    fderivWithin_of_isOpen l4Slab_isOpen hp]

theorem l4G_cdOn (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun y : ℝ × (ℝ × ℝ) => -(fderivWithin ℝ (gaussQ κ ν) l4Slab y)) l4Slab :=
  ((l4Q_cdOn κ ν hκ hν (n + 1)).fderivWithin l4Slab_uniq (le_refl _)).neg

theorem l4G_norm (κ ν : ℝ) (k : ℕ) {p : ℝ × (ℝ × ℝ)} (hp : p ∈ l4Slab) :
    ‖iteratedFDerivWithin ℝ k
        (fun y : ℝ × (ℝ × ℝ) => -(fderivWithin ℝ (gaussQ κ ν) l4Slab y)) l4Slab p‖
      = ‖iteratedFDeriv ℝ (k + 1) (gaussQ κ ν) p‖ := by
  have h1 : (fun y : ℝ × (ℝ × ℝ) => -(fderivWithin ℝ (gaussQ κ ν) l4Slab y)) =
      -(fderivWithin ℝ (gaussQ κ ν) l4Slab) := rfl
  rw [h1, iteratedFDerivWithin_neg_apply l4Slab_uniq hp, norm_neg,
    norm_iteratedFDerivWithin_fderivWithin l4Slab_uniq hp,
    iteratedFDerivWithin_of_isOpen (k + 1) l4Slab_isOpen hp]

/-- Real-number form of one Leibniz term. -/
theorem l4_leib_term (c C Dn nA nB a p e P : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) (hD : 0 ≤ Dn)
    (hp : 0 ≤ p) (he : 0 ≤ e) (hnB : 0 ≤ nB) (hA : nA ≤ C * p * e) (hB : nB ≤ Dn * a)
    (hpow : p * a ≤ P) : c * nA * nB ≤ c * C * Dn * P * e := by
  calc c * nA * nB ≤ c * (C * p * e) * (Dn * a) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA hc) hB hnB
          (mul_nonneg hc (mul_nonneg (mul_nonneg hC hp) he))
    _ = (c * C * Dn) * (p * a) * e := by ring
    _ ≤ (c * C * Dn) * P * e :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hc hC) hD)) he

theorem gaussExpStep_proof (κ ν s0 s1 : ℝ) : GaussExpStep κ ν s0 s1 := by
  intro hκ hν hs0 hs01 hQ
  choose D hD0 hD using hQ hκ hν hs0 hs01
  have key : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ,
      ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p)))
          l4Slab (s, x)‖
        ≤ C * (1 + sq2 x) ^ i * Real.exp (-(gaussQ κ ν (s, x))) := by
    intro m
    induction m with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro i hi s hs x
      obtain rfl : i = 0 := by omega
      rw [norm_iteratedFDerivWithin_zero]
      simp
    | succ m ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * C * D (m - i + 1) := ⟨_, rfl⟩
      have hTop : ∀ s ∈ Set.Icc s0 s1, ∀ x : ℝ × ℝ,
          ‖iteratedFDerivWithin ℝ (m + 1)
              (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) l4Slab (s, x)‖
            ≤ K * (1 + sq2 x) ^ (m + 1) * Real.exp (-(gaussQ κ ν (s, x))) := by
        intro s hs x
        have hsp : (s, x) ∈ l4Slab := by
          show (0 : ℝ) < s
          exact lt_of_lt_of_le hs0 hs.1
        have ha0 : 0 ≤ 1 + sq2 x := by
          have := l4_sq2_nonneg x
          linarith
        have ha1 : (1 : ℝ) ≤ 1 + sq2 x := by
          have := l4_sq2_nonneg x
          linarith
        have hEq : EqOn (fderivWithin ℝ
              (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) l4Slab)
            (fun y : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν y)) •
              -(fderivWithin ℝ (gaussQ κ ν) l4Slab y)) l4Slab :=
          fun y hy => l4E_fderivWithin κ ν hκ hν hy
        have hstep : ‖iteratedFDerivWithin ℝ (m + 1)
              (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) l4Slab (s, x)‖
            = ‖iteratedFDerivWithin ℝ m
                (fun y : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν y)) •
                  -(fderivWithin ℝ (gaussQ κ ν) l4Slab y)) l4Slab (s, x)‖ := by
          rw [← norm_iteratedFDerivWithin_fderivWithin l4Slab_uniq hsp,
            iteratedFDerivWithin_congr hEq hsp m]
        rw [hstep]
        have hf : ContDiffOn ℝ (m : WithTop ℕ∞)
            (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) l4Slab :=
          l4E_cdOn κ ν hκ hν _
        have hg : ContDiffOn ℝ (m : WithTop ℕ∞)
            (fun y : ℝ × (ℝ × ℝ) => -(fderivWithin ℝ (gaussQ κ ν) l4Slab y)) l4Slab :=
          l4G_cdOn κ ν hκ hν _
        refine le_trans
          (norm_iteratedFDerivWithin_smul_le (n := m) hf hg l4Slab_uniq hsp (le_refl _)) ?_
        have hterm : ∀ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) *
                ‖iteratedFDerivWithin ℝ i
                    (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(gaussQ κ ν p))) l4Slab (s, x)‖ *
              ‖iteratedFDerivWithin ℝ (m - i)
                  (fun y : ℝ × (ℝ × ℝ) => -(fderivWithin ℝ (gaussQ κ ν) l4Slab y))
                  l4Slab (s, x)‖
            ≤ ((m.choose i : ℝ) * C * D (m - i + 1)) * (1 + sq2 x) ^ (m + 1)
                * Real.exp (-(gaussQ κ ν (s, x))) := by
          intro i hi
          have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have h1 := hC i hi' s hs x
          have h2 : ‖iteratedFDerivWithin ℝ (m - i)
                (fun y : ℝ × (ℝ × ℝ) => -(fderivWithin ℝ (gaussQ κ ν) l4Slab y))
                l4Slab (s, x)‖ ≤ D (m - i + 1) * (1 + sq2 x) := by
            rw [l4G_norm κ ν (m - i) hsp]
            exact hD (m - i + 1) s hs x
          have hpow : (1 + sq2 x) ^ i * (1 + sq2 x) ≤ (1 + sq2 x) ^ (m + 1) := by
            rw [← pow_succ]
            exact pow_le_pow_right₀ ha1 (by omega)
          exact l4_leib_term _ C _ _ _ _ _ _ _ (Nat.cast_nonneg _) hC0 (hD0 _)
            (pow_nonneg ha0 _) (Real.exp_pos _).le (norm_nonneg _) h1 h2 hpow
        refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
        rw [hKdef, Finset.sum_mul, Finset.sum_mul]
      refine ⟨max C K, le_max_of_le_left hC0, ?_⟩
      intro i hi s hs x
      rcases (show i ≤ m ∨ i = m + 1 by omega) with h | h
      · have h1 := hC i h s hs x
        have h2 : C * (1 + sq2 x) ^ i * Real.exp (-(gaussQ κ ν (s, x)))
            ≤ max C K * (1 + sq2 x) ^ i * Real.exp (-(gaussQ κ ν (s, x))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (pow_nonneg (by unfold sq2; positivity) _))
            (Real.exp_pos _).le
        exact h1.trans h2
      · subst h
        have h1 := hTop s hs x
        have h2 : K * (1 + sq2 x) ^ (m + 1) * Real.exp (-(gaussQ κ ν (s, x)))
            ≤ max C K * (1 + sq2 x) ^ (m + 1) * Real.exp (-(gaussQ κ ν (s, x))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _)
              (pow_nonneg (by unfold sq2; positivity) _))
            (Real.exp_pos _).le
        exact h1.trans h2
  intro m
  obtain ⟨C, hC0, hC⟩ := key m
  refine ⟨C, hC0, fun s hs x => ?_⟩
  have hsp : (s, x) ∈ l4Slab := by
    show (0 : ℝ) < s
    exact lt_of_lt_of_le hs0 hs.1
  rw [← iteratedFDerivWithin_of_isOpen m l4Slab_isOpen hsp]
  exact hC m le_rfl s hs x

end UnforcedLeray.Short.PartIIIb.Concrete
