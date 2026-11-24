import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2_3

/-!
# Part II-b, leaf `PartII-b:G4/3/6/2/3/4`: `PsiD2Jet`

Source of record: `the November 2 reference manuscript` 2419-2423 and 261-291.
For `s > 0` the stream relation gives `Dψ_s(h) = h₁ v₁ - h₂ v₀` at every point, so
`D²ψ_s(d)(h) = h₁ Dv₁(d) - h₂ Dv₀(d)` and `‖D²ψ_s‖ ≤ 2‖Dv‖` on the sup-norm plane.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.IIb

private theorem d2_fderiv_apply_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {y : E} (hF : DifferentiableAt ℝ (fderiv ℝ F) y) (v e : E) :
    fderiv ℝ (fun z => fderiv ℝ F z v) y e = fderiv ℝ (fderiv ℝ F) y e v := by
  rw [fderiv_clm_apply hF (differentiableAt_const v)]
  simp

theorem psiD2Jet_core : PsiD2Jet := by
  intro ψ v hsp s hs z
  obtain ⟨hΨ, hV, hst⟩ := hsp
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : ∀ w : ℝ × ℝ, (s, w) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    fun w => ⟨hs, Set.mem_univ _⟩
  have hinc : ∀ w : ℝ × ℝ, ContDiffAt ℝ ∞ (fun w' : ℝ × ℝ => ((s, w') : ℝ × (ℝ × ℝ))) w :=
    fun w => (contDiffAt_const (c := s)).prodMk contDiffAt_id
  have hgc : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 (fun w' => ψ s w') w := by
    intro w
    have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => ψ x.1 x.2) (s, w) :=
      hΨ.contDiffAt (hopen.mem_nhds (hmem w))
    exact (h0.comp w (hinc w)).of_le (by simp)
  have hvc : ∀ w : ℝ × ℝ, ContDiffAt ℝ 2 (fun w' => v s w') w := by
    intro w
    have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => v x.1 x.2) (s, w) :=
      hV.contDiffAt (hopen.mem_nhds (hmem w))
    exact (h0.comp w (hinc w)).of_le (by simp)
  have hdiff : ∀ w : ℝ × ℝ, DifferentiableAt ℝ (fun w' => ψ s w') w :=
    fun w => (hgc w).differentiableAt (by norm_num)
  have hfd : ∀ w : ℝ × ℝ, DifferentiableAt ℝ (fderiv ℝ (fun w' => ψ s w')) w :=
    fun w => ((hgc w).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvd : ∀ w : ℝ × ℝ, DifferentiableAt ℝ (fun w' => v s w') w :=
    fun w => (hvc w).differentiableAt (by norm_num)
  -- Cartesian partials of `ψ s` through the stream relation
  have hX : ∀ w : ℝ × ℝ, fderiv ℝ (fun w' => ψ s w') w (1, 0) = v s w 1 := by
    intro w
    have hγ : HasDerivAt (fun x : ℝ => ((x, w.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) w.1 :=
      (hasDerivAt_id' w.1).prodMk (hasDerivAt_const w.1 w.2)
    have h : HasDerivAt (fun x : ℝ => ψ s (x, w.2)) (fderiv ℝ (fun w' => ψ s w') w (1, 0)) w.1 := by
      have h' := (hdiff w).hasFDerivAt.comp_hasDerivAt w.1 hγ
      exact h'
    have hv : v s w 1 = deriv (fun x : ℝ => ψ s (x, w.2)) w.1 := by
      rw [hst s hs w]
      rfl
    rw [hv, h.deriv]
  have hY : ∀ w : ℝ × ℝ, fderiv ℝ (fun w' => ψ s w') w (0, 1) = -(v s w 0) := by
    intro w
    have hγ : HasDerivAt (fun y : ℝ => ((w.1, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) w.2 :=
      (hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id' w.2)
    have h : HasDerivAt (fun y : ℝ => ψ s (w.1, y)) (fderiv ℝ (fun w' => ψ s w') w (0, 1)) w.2 :=
      (hdiff w).hasFDerivAt.comp_hasDerivAt w.2 hγ
    have hv : v s w 0 = -(deriv (fun y : ℝ => ψ s (w.1, y)) w.2) := by
      rw [hst s hs w]
      rfl
    rw [hv, neg_neg, h.deriv]
  have hlin : ∀ (w h : ℝ × ℝ), fderiv ℝ (fun w' => ψ s w') w h = h.1 * v s w 1 - h.2 * v s w 0 := by
    intro w h
    have hsplit : h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hX, hY]
    ring
  -- second derivative: `D²ψ(d)(h) = h₁ Dv₁(d) - h₂ Dv₀(d)`
  have hd2 : ∀ (w d h : ℝ × ℝ),
      fderiv ℝ (fderiv ℝ (fun w' => ψ s w')) w d h =
        h.1 * fderiv ℝ (fun w' => v s w') w d 1 - h.2 * fderiv ℝ (fun w' => v s w') w d 0 := by
    intro w d h
    rw [← d2_fderiv_apply_symm (hfd w) h d]
    have hfun : (fun z => fderiv ℝ (fun w' => ψ s w') z h) =
        fun z => h.1 * v s z 1 - h.2 * v s z 0 :=
      funext fun z => hlin z h
    rw [hfun]
    let Lp : Fin 2 → (UnforcedLeray.Train.Vec →L[ℝ] ℝ) := fun i => EuclideanSpace.proj i
    have hc1 : HasFDerivAt (fun z => v s z 1) ((Lp 1).comp (fderiv ℝ (fun w' => v s w') w)) w :=
      (Lp 1).hasFDerivAt.comp w (hvd w).hasFDerivAt
    have hc0 : HasFDerivAt (fun z => v s z 0) ((Lp 0).comp (fderiv ℝ (fun w' => v s w') w)) w :=
      (Lp 0).hasFDerivAt.comp w (hvd w).hasFDerivAt
    have hcomb : HasFDerivAt (fun z => h.1 * v s z 1 - h.2 * v s z 0)
        (h.1 • (Lp 1).comp (fderiv ℝ (fun w' => v s w') w) -
          h.2 • (Lp 0).comp (fderiv ℝ (fun w' => v s w') w)) w :=
      (hc1.const_mul h.1).sub (hc0.const_mul h.2)
    rw [hcomb.fderiv]
    rfl
  -- the bound for the second derivative in terms of `‖Dv‖`
  have hbound : ∀ (w d h : ℝ × ℝ),
      ‖fderiv ℝ (fderiv ℝ (fun w' => ψ s w')) w d h‖ ≤
        2 * ‖fderiv ℝ (fun w' => v s w') w‖ * ‖d‖ * ‖h‖ := by
    intro w d h
    rw [hd2 w d h, Real.norm_eq_abs]
    have hA : |fderiv ℝ (fun w' => v s w') w d 1| ≤ ‖fderiv ℝ (fun w' => v s w') w d‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ 1
    have hB : |fderiv ℝ (fun w' => v s w') w d 0| ≤ ‖fderiv ℝ (fun w' => v s w') w d‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le _ 0
    have hD : ‖fderiv ℝ (fun w' => v s w') w d‖ ≤
        ‖fderiv ℝ (fun w' => v s w') w‖ * ‖d‖ :=
      (fderiv ℝ (fun w' => v s w') w).le_opNorm d
    have h1 : |h.1| ≤ ‖h‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_fst_le h
    have h2 : |h.2| ≤ ‖h‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_snd_le h
    have hsum : |h.1 * fderiv ℝ (fun w' => v s w') w d 1 - h.2 * fderiv ℝ (fun w' => v s w') w d 0|
        ≤ |h.1| * |fderiv ℝ (fun w' => v s w') w d 1| +
          |h.2| * |fderiv ℝ (fun w' => v s w') w d 0| := by
      calc _ ≤ |h.1 * fderiv ℝ (fun w' => v s w') w d 1| +
            |h.2 * fderiv ℝ (fun w' => v s w') w d 0| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul]
    have hAB : |fderiv ℝ (fun w' => v s w') w d 1| + |fderiv ℝ (fun w' => v s w') w d 0| ≤
        2 * (‖fderiv ℝ (fun w' => v s w') w‖ * ‖d‖) := by
      linarith
    calc _ ≤ |h.1| * |fderiv ℝ (fun w' => v s w') w d 1| +
          |h.2| * |fderiv ℝ (fun w' => v s w') w d 0| := hsum
      _ ≤ ‖h‖ * |fderiv ℝ (fun w' => v s w') w d 1| +
          ‖h‖ * |fderiv ℝ (fun w' => v s w') w d 0| :=
        add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
      _ = ‖h‖ * (|fderiv ℝ (fun w' => v s w') w d 1| +
          |fderiv ℝ (fun w' => v s w') w d 0|) := by ring
      _ ≤ ‖h‖ * (2 * (‖fderiv ℝ (fun w' => v s w') w‖ * ‖d‖)) :=
        mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
      _ = 2 * ‖fderiv ℝ (fun w' => v s w') w‖ * ‖d‖ * ‖h‖ := by ring
  -- the bound on the multilinear second derivative
  have hD2 : ‖iteratedFDeriv ℝ 2 (fun w' => ψ s w') z‖ ≤
      2 * ‖fderiv ℝ (fun w' => v s w') z‖ := by
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro m
    rw [iteratedFDeriv_two_apply, Fin.prod_univ_two]
    calc _ ≤ 2 * ‖fderiv ℝ (fun w' => v s w') z‖ * ‖m 0‖ * ‖m 1‖ := hbound z (m 0) (m 1)
      _ = 2 * ‖fderiv ℝ (fun w' => v s w') z‖ * (‖m 0‖ * ‖m 1‖) := by ring
  have e2 : ageJet 0 2 ψ s z = iteratedFDeriv ℝ 2 (fun w' => ψ s w') z := by
    simp only [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero]
  have e1 : ageJet 0 1 v s z = iteratedFDeriv ℝ 1 (fun w' => v s w') z := by
    simp only [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet, iteratedDeriv_zero]
  rw [e2, e1, norm_iteratedFDeriv_one]
  exact hD2

end UnforcedLeray.Short.IIb

/-- **Jet `(0,2)`** (SP 2419-2423), leaf `PartII-b:G4/3/6/2/3/4`. -/
theorem psiD2Jet_proof : UnforcedLeray.Short.IIb.PsiD2Jet :=
  UnforcedLeray.Short.IIb.psiD2Jet_core
