import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L2

/-!
# `HpPsiEnv` from the gradient-piece lattice envelopes (`PartIII-b:C/asrc/ra/9/2/2/12`)

Source of record: `the November 2 reference manuscript`, lines 4963-4980,
5036-5039, 5063-5079.

The six quantities of `HpPsiEnv` (`h^p_A`, `D_x h^p_A`, `𝒦h^p_A`, `k = (1-𝒦)ψ^p_A`, `D_x k`, `𝒦k`)
are linear combinations of `u, dQ u, dEta u, Kop u` for `u = (h^p_A)_{r,z}`, and of `ψ^p_A`,
`dQ, dEta, Kop` of `ψ^p_A` and of `𝒦ψ^p_A`, `Kop (𝒦ψ^p_A)`: exactly the quantities enveloped
by the grad-piece Props `GradLatticeHp`, `GradLatticePsi` (weight
`gradF ≤ s^{5/2} M(A)`), with differentiability from `GradLatticeSmooth`.
Proved: `hpPsiEnv_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `|A^y| + |s∂_sA^y| + |(s∂_s)²A^y| ≤ s^{5/2} M(A)` on `0 < s ≤ 1.1/ν`. -/
theorem hpe_gradF_le (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3)
    (hBdd : BddAbove ((fun s => s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s) ''
      Ioc 0 ((11 / 10) / ν)))
    (s : ℝ) (hs : 0 < s) (hsT : s ≤ (11 / 10) / ν) :
    gradF ν χ A s ≤ s ^ (5 / 2 : ℝ) * affM ν χ A := by
  have hle : s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s ≤ affM ν χ A :=
    le_csSup hBdd ⟨s, ⟨hs, hsT⟩, rfl⟩
  have hge : frob (sDerivIter 0 (Ay ν χ A) s) + frob (sDerivIter 1 (Ay ν χ A) s) +
      frob (sDerivIter 2 (Ay ν χ A) s) ≤ affSum 6 (Ay ν χ A) s := by
    have hp : ∑ j ∈ ({0, 1, 2} : Finset ℕ), frob (sDerivIter j (Ay ν χ A) s) =
        frob (sDerivIter 0 (Ay ν χ A) s) + frob (sDerivIter 1 (Ay ν χ A) s) +
          frob (sDerivIter 2 (Ay ν χ A) s) := by
      rw [Finset.sum_insert (by norm_num), Finset.sum_pair (by norm_num)]; ring
    have hs' : ∑ j ∈ ({0, 1, 2} : Finset ℕ), frob (sDerivIter j (Ay ν χ A) s) ≤
        ∑ j ∈ Finset.range (6 + 1), frob (sDerivIter j (Ay ν χ A) s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> simp
      · intro i _ _
        exact Real.sqrt_nonneg _
    unfold affSum
    linarith
  have hr : s ^ (-(5 / 2 : ℝ)) = (s ^ (5 / 2 : ℝ))⁻¹ := Real.rpow_neg hs.le _
  have hpos : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have e0 : gradF ν χ A s = frob (sDerivIter 0 (Ay ν χ A) s) + frob (sDerivIter 1 (Ay ν χ A) s) +
      frob (sDerivIter 2 (Ay ν χ A) s) := rfl
  rw [e0]
  calc _ ≤ affSum 6 (Ay ν χ A) s := hge
    _ = s ^ (5 / 2 : ℝ) * (s ^ (-(5 / 2 : ℝ)) * affSum 6 (Ay ν χ A) s) := by
        rw [hr, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ s ^ (5 / 2 : ℝ) * affM ν χ A := mul_le_mul_of_nonneg_left hle hpos.le

/-- Operator norm of a linear map on `ℝ × ℝ` from its values on the two basis vectors. -/
theorem hpe_opNorm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ × ℝ →L[ℝ] F) {B : ℝ} (h0 : ‖L (ei 0)‖ ≤ B) (h1 : ‖L (ei 1)‖ ≤ B) :
    ‖L‖ ≤ 2 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans h0
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
  have hw : w = w.1 • ei 0 + w.2 • ei 1 := by ext <;> simp [ei]
  have e : L w = w.1 • L (ei 0) + w.2 • L (ei 1) := by
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul]
  rw [e]
  have a1 : |w.1| ≤ ‖w‖ := by simpa using norm_fst_le w
  have a2 : |w.2| ≤ ‖w‖ := by simpa using norm_snd_le w
  calc ‖w.1 • L (ei 0) + w.2 • L (ei 1)‖ ≤ ‖w.1 • L (ei 0)‖ + ‖w.2 • L (ei 1)‖ :=
        norm_add_le _ _
    _ = |w.1| * ‖L (ei 0)‖ + |w.2| * ‖L (ei 1)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖w‖ * B + ‖w‖ * B := by
        gcongr
    _ = 2 * B * ‖w‖ := by ring

theorem hpe_fst {f : ℝ × ℝ → ℝ × ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) (w : ℝ × ℝ) :
    fderiv ℝ (fun y => (f y).1) x w = (fderiv ℝ f x w).1 := by
  rw [hf.hasFDerivAt.fst.fderiv]; rfl

theorem hpe_snd {f : ℝ × ℝ → ℝ × ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) (w : ℝ × ℝ) :
    fderiv ℝ (fun y => (f y).2) x w = (fderiv ℝ f x w).2 := by
  rw [hf.hasFDerivAt.snd.fderiv]; rfl

theorem hpe_prod_norm_le {p : ℝ × ℝ} {B : ℝ} (h1 : |p.1| ≤ B) (h2 : |p.2| ≤ B) : ‖p‖ ≤ B := by
  rw [Prod.norm_def]
  exact max_le (by simpa using h1) (by simpa using h2)

theorem hpe_contDiffAt (ν : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) (A : ℝ → Mat3)
    (hA : ContDiffOn ℝ 6 A (Ioi 0)) (s : ℝ) (hs : 0 < s) :
    ContDiffAt ℝ 2 (Ay ν χf A) s := by
  have hAcd : ContDiffAt ℝ 2 A s :=
    (hA.contDiffAt (Ioi_mem_nhds hs)).of_le (by norm_num)
  have hχ2 : ContDiff ℝ 2 χf := (contDiff_infty.mp hχ.smooth) 2
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => χf (ν * t)) s :=
    (hχ2.contDiffAt (x := ν * s)).comp s (contDiffAt_const.mul contDiffAt_id)
  exact hc.smul hAcd

theorem hpPsiEnv_of (h1 : GradLatticeHp) (h2 : GradLatticePsi) (h3 : GradLatticeSmooth)
    (as : ℝ) : HpPsiEnv as := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  set C0 : ℝ := max C1 C2 with hC0
  have hC0nn : 0 ≤ C0 := hC1.trans (le_max_left _ _)
  refine ⟨4 * C0, gradAlpha, gradK, by positivity, by norm_num [gradAlpha], ?_⟩
  intro χf hχ ν hν hν1 A hA s hs hsT x
  have hbdd := aySumBdd_inst11 as χf hχ ν hν A hA
  have hd : GradData ν s χf A := ⟨hν, hν1, hs, hsT, hpe_contDiffAt ν χf hχ A hA.smooth s hs⟩
  have hF := hpe_gradF_le ν χf A hbdd s hs hsT
  set L : ℝ := latticeS gradAlpha gradK (cOf ν) x with hLdef
  have hL : 0 ≤ L := tsum_nonneg (fun j => by unfold latticeW; positivity)
  have hM0 : 0 ≤ affM ν χf A := affM_nonneg ν χf A
  set E : ℝ := affM ν χf A * s ^ (5 / 2 : ℝ) * L with hEdef
  have hE : 0 ≤ E := by
    have : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    positivity
  have hCE : 0 ≤ C0 * E := mul_nonneg hC0nn hE
  have bound : ∀ C : ℝ, 0 ≤ C → C ≤ C0 → C * gradF ν χf A s * L ≤ C0 * E := by
    intro C hC hCC
    have hg0 : 0 ≤ gradF ν χf A s := by
      exact add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have h1' : gradF ν χf A s * L ≤ (s ^ (5 / 2 : ℝ) * affM ν χf A) * L :=
      mul_le_mul_of_nonneg_right hF hL
    calc C * gradF ν χf A s * L = C * (gradF ν χf A s * L) := by ring
      _ ≤ C0 * ((s ^ (5 / 2 : ℝ) * affM ν χf A) * L) :=
          mul_le_mul hCC h1' (mul_nonneg hg0 hL) hC0nn
      _ = C0 * E := by rw [hEdef]; ring
  have b1 : ∀ t : ℝ, t ≤ C1 * gradF ν χf A s * L → t ≤ C0 * E := fun t ht =>
    ht.trans (bound C1 hC1 (le_max_left _ _))
  have b2 : ∀ t : ℝ, t ≤ C2 * gradF ν χf A s * L → t ≤ C0 * E := fun t ht =>
    ht.trans (bound C2 hC2 (le_max_right _ _))
  -- envelopes
  obtain ⟨r0, r1, r2, r3⟩ := H1 ν s χf A hd x (hpR ν χf A) (Or.inl rfl)
  obtain ⟨z0, z1, z2, z3⟩ := H1 ν s χf A hd x (hpZ ν χf A) (Or.inr rfl)
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := H2 ν s χf A hd x
  -- smoothness
  obtain ⟨sr, sr'⟩ := h3 ν s χf A hd x (hpR ν χf A) (Or.inl rfl)
  obtain ⟨sz, sz'⟩ := h3 ν s χf A hd x (hpZ ν χf A) (Or.inr (Or.inl rfl))
  obtain ⟨sp, sp'⟩ := h3 ν s χf A hd x (psipA ν χf A) (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨sg, sg'⟩ := h3 ν s χf A hd x (fun s' y => Kop (psipA ν χf A) s' y)
    (Or.inr (Or.inr (Or.inr rfl)))
  have hD : DifferentiableAt ℝ (hpA ν χf A s) x := sr.prodMk sz
  have hfd1 : ∀ w, fderiv ℝ (hpR ν χf A s) x w = (fderiv ℝ (hpA ν χf A s) x w).1 :=
    fun w => hpe_fst hD w
  have hfd2 : ∀ w, fderiv ℝ (hpZ ν χf A s) x w = (fderiv ℝ (hpA ν χf A s) x w).2 :=
    fun w => hpe_snd hD w
  have hr0 := b1 _ r0
  have hr1 := b1 _ r1
  have hr2 := b1 _ r2
  have hr3 := b1 _ r3
  have hz0 := b1 _ z0
  have hz1 := b1 _ z1
  have hz2 := b1 _ z2
  have hz3 := b1 _ z3
  have hp0 := b2 _ p0
  have hp1 := b2 _ p1
  have hp2 := b2 _ p2
  have hp3 := b2 _ p3
  have hp4 := b2 _ p4
  have hp5 := b2 _ p5
  have hp6 := b2 _ p6
  have hfin : C0 * E ≤ 4 * C0 * affM ν χf A * s ^ (5 / 2 : ℝ) * L := by
    rw [hEdef]; nlinarith [mul_nonneg hC0nn hE, hEdef]
  have hfinE : 4 * C0 * affM ν χf A * s ^ (5 / 2 : ℝ) * L = 4 * (C0 * E) := by
    rw [hEdef]; ring
  rw [hfinE]
  -- differentiability facts for k
  have hKfd : fderiv ℝ (kOf ν χf A s) x =
      fderiv ℝ (psipA ν χf A s) x - fderiv ℝ (fun y => Kop (psipA ν χf A) s y) x :=
    fderiv_sub sp sg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- h^p
    refine (hpe_prod_norm_le (B := C0 * E) hr0 hz0).trans ?_
    linarith
  · -- D_x h^p
    have e0 : ‖fderiv ℝ (hpA ν χf A s) x (ei 0)‖ ≤ C0 * E := by
      refine hpe_prod_norm_le ?_ ?_
      · rw [← hfd1]; exact hr1
      · rw [← hfd2]; exact hz1
    have e1 : ‖fderiv ℝ (hpA ν χf A s) x (ei 1)‖ ≤ C0 * E := by
      refine hpe_prod_norm_le ?_ ?_
      · rw [← hfd1]; exact hr2
      · rw [← hfd2]; exact hz2
    have := hpe_opNorm_le _ e0 e1
    linarith
  · -- 𝒦 h^p
    refine (hpe_prod_norm_le (B := C0 * E) hr3 hz3).trans ?_
    linarith
  · -- k
    show |psipA ν χf A s x - Kop (fun s' y => psipA ν χf A s' y) s x| ≤ _
    have := abs_sub (psipA ν χf A s x) (Kop (fun s' y => psipA ν χf A s' y) s x)
    have h3' : |Kop (fun s' y => psipA ν χf A s' y) s x| ≤ C0 * E := hp3
    linarith
  · -- D_x k
    have ev : ∀ a : Fin 2, ‖fderiv ℝ (kOf ν χf A s) x (ei a)‖ ≤ 2 * (C0 * E) →
        True := fun _ _ => trivial
    have e0 : ‖fderiv ℝ (kOf ν χf A s) x (ei 0)‖ ≤ 2 * (C0 * E) := by
      rw [hKfd, sub_apply, Real.norm_eq_abs]
      have a := abs_sub (fderiv ℝ (psipA ν χf A s) x (ei 0))
        (fderiv ℝ (fun y => Kop (psipA ν χf A) s y) x (ei 0))
      have b : |fderiv ℝ (psipA ν χf A s) x (ei 0)| ≤ C0 * E := hp1
      have c : |fderiv ℝ (fun y => Kop (psipA ν χf A) s y) x (ei 0)| ≤ C0 * E := hp4
      linarith
    have e1 : ‖fderiv ℝ (kOf ν χf A s) x (ei 1)‖ ≤ 2 * (C0 * E) := by
      rw [hKfd, sub_apply, Real.norm_eq_abs]
      have a := abs_sub (fderiv ℝ (psipA ν χf A s) x (ei 1))
        (fderiv ℝ (fun y => Kop (psipA ν χf A) s y) x (ei 1))
      have b : |fderiv ℝ (psipA ν χf A s) x (ei 1)| ≤ C0 * E := hp2
      have c : |fderiv ℝ (fun y => Kop (psipA ν χf A) s y) x (ei 1)| ≤ C0 * E := hp5
      linarith
    have := hpe_opNorm_le _ e0 e1
    linarith
  · -- 𝒦 k
    have hK : Kop (kOf ν χf A) s x = Kop (psipA ν χf A) s x -
        Kop (fun s' y => Kop (psipA ν χf A) s' y) s x := by
      have hder : deriv (fun s' => kOf ν χf A s' x) s =
          deriv (fun s' => psipA ν χf A s' x) s -
            deriv (fun s' => Kop (psipA ν χf A) s' x) s :=
        deriv_sub sp' sg'
      show x.2 * fderiv ℝ (kOf ν χf A s) x (ei 1) +
          2 * s * deriv (fun s' => kOf ν χf A s' x) s =
        (x.2 * fderiv ℝ (psipA ν χf A s) x (ei 1) + 2 * s * deriv (fun s' => psipA ν χf A s' x) s) -
          (x.2 * fderiv ℝ (fun y => Kop (psipA ν χf A) s y) x (ei 1) +
            2 * s * deriv (fun s' => Kop (psipA ν χf A) s' x) s)
      rw [hKfd, hder, sub_apply]
      ring
    rw [hK]
    have a := abs_sub (Kop (psipA ν χf A) s x)
      (Kop (fun s' y => Kop (psipA ν χf A) s' y) s x)
    have b : |Kop (psipA ν χf A) s x| ≤ C0 * E := hp3
    have c : |Kop (fun s' y => Kop (psipA ν χf A) s' y) s x| ≤ C0 * E := hp6
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete
