import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.HeatIdentity.Heat

/-!
# Leaf `PartII-b:T11/2/2/3` (`DualHeatIdentity`)

Pointwise identity `T(∇^⊥ψ_∞) = -σ^μ χ'(σ) ∇^⊥g` (SP 1923-1927), `ψ_∞ = a(σ) G`,
`a = σ^{μ-1}χ`, `G(σ,·) = H(s-σ,·)`.  On the slab `0 < σ < s`: `∂_q, ∂_η` pass through `a`,
`∂_σ(aF) = a'F + a∂_σF`; with `G_σ = -νΔG` (and its `∂_d`-derivative) the bracket collapses to
`[(μ-1)a - σa'] ∂_dG = -σ^μχ' ∂_dG`.  Outside `tsupport χ` both sides vanish.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cpdC_zero_on' {V : Set Coord} (hV : IsOpen V) {F : Coord → ℂ}
    (hF : ∀ y ∈ V, F y = 0) (j : Fin 3) : ∀ y ∈ V, cpdC j F y = 0 := by
  intro y hy
  have := cpdC_congr_on hV (g := fun _ => (0 : ℂ)) hF j y hy
  rw [this]; simp [cpdC]

theorem flatTransposeC_zero_on {V : Set Coord} (hV : IsOpen V) (ν : ℝ) (μ : ℂ)
    (Ψ : Coord → Fin 2 → ℂ) (hΨ : ∀ y ∈ V, ∀ i, Ψ y i = 0) (x : Coord) (hx : x ∈ V) (i : Fin 2) :
    flatTransposeC ν μ Ψ x i = 0 := by
  have h0 : ∀ y ∈ V, Ψ y i = 0 := fun y hy => hΨ y hy i
  have z0 := cpdC_zero_on' hV (F := fun y => Ψ y i) h0 0 x hx
  have z1 := cpdC_zero_on' hV (cpdC_zero_on' hV (F := fun y => Ψ y i) h0 1) 1 x hx
  have z2 := cpdC_zero_on' hV (cpdC_zero_on' hV (F := fun y => Ψ y i) h0 2) 2 x hx
  unfold flatTransposeC
  rw [h0 x hx, z0, z1, z2]; simp

/-- the `d`-th core identity (`d ∈ {1,2}`, `(cdir d).1 = 0`). -/
theorem dual_core {c ν r' : ℝ} (μ : ℂ) {H : Coord → ℝ} {s : ℝ} {χ : ℝ → ℝ}
    (hH : HeatSol c ν r' H) (hχ : ContDiff ℝ ∞ χ) (d : Fin 3) (hd : (cdir d).1 = 0)
    (x : Coord) (hx : x ∈ dtW s) :
    (μ - 1) * cpdC d (dualPsiInf μ χ H s) x -
      (x.1 : ℂ) * cpdC 0 (cpdC d (dualPsiInf μ χ H s)) x -
      (ν : ℂ) * (x.1 : ℂ) * (cpdC 1 (cpdC 1 (cpdC d (dualPsiInf μ χ H s))) x +
        cpdC 2 (cpdC 2 (cpdC d (dualPsiInf μ χ H s))) x) =
    -(((x.1 : ℂ) ^ μ) * ((deriv χ x.1 : ℝ) : ℂ) *
        cpdC d (fun z => ((H (s - z.1, z.2) : ℝ) : ℂ)) x) := by
  have hW := isOpen_dtW s
  set a : ℝ → ℂ := fun u => (u : ℂ) ^ (μ - 1) * (χ u : ℂ) with ha_def
  set G : Coord → ℝ := dtG H s with hG_def
  set Gc : Coord → ℂ := fun y => (G y : ℂ) with hGc_def
  set ψ : Coord → ℂ := dualPsiInf μ χ H s with hψ_def
  have hχd : ∀ t, DifferentiableAt ℝ χ t := fun t => (hχ.differentiable (by norm_num)) t
  have hpos : ∀ y ∈ dtW s, 0 < y.1 := fun y hy => hy.1.1
  have ha : ∀ y ∈ dtW s, DifferentiableAt ℝ a y.1 := fun y hy =>
    (hasDerivAt_dualA μ χ y.1 (hpos y hy) (hχd _)).differentiableAt
  have hGs : ContDiffOn ℝ ∞ G (dtW s) := dtG_contDiffOn hH.smooth
  have hGcs : ContDiffOn ℝ ∞ Gc (dtW s) := Complex.ofRealCLM.contDiff.comp_contDiffOn hGs
  have hψ : ∀ y ∈ dtW s, ψ y = a y.1 * Gc y := fun y _ => rfl
  -- level 1
  have F1 : ∀ y ∈ dtW s, cpdC d ψ y = a y.1 * cpdC d Gc y :=
    cpdC_mul_a_qeta hW a ha hψ hGcs d hd
  have c1 := cpdC_contDiffOn' hW hGcs d
  -- level 2 (`q`, `η` derivatives)
  have F2 : ∀ j : Fin 3, (cdir j).1 = 0 → ∀ y ∈ dtW s,
      cpdC j (cpdC d ψ) y = a y.1 * cpdC j (cpdC d Gc) y := fun j hj =>
    cpdC_mul_a_qeta hW a ha F1 c1 j hj
  have F3 : ∀ j k : Fin 3, (cdir j).1 = 0 → (cdir k).1 = 0 → ∀ y ∈ dtW s,
      cpdC k (cpdC j (cpdC d ψ)) y = a y.1 * cpdC k (cpdC j (cpdC d Gc)) y := fun j k hj hk =>
    cpdC_mul_a_qeta hW a ha (F2 j hj) (cpdC_contDiffOn' hW c1 j) k hk
  have F0 := cpdC_mul_a_s hW a ha F1 c1 x hx
  have h1 : (cdir 1).1 = 0 := by simp [cdir]
  have h2 : (cdir 2).1 = 0 := by simp [cdir]
  rw [F0, F1 x hx, F3 1 1 h1 h1 x hx, F3 2 2 h2 h2 x hx]
  -- real transfer
  have R1 : ∀ y ∈ dtW s, cpdC d Gc y = (cpd d G y : ℂ) :=
    cpdC_ofReal_on hW hGs (fun y _ => rfl) d
  have R2 : ∀ j : Fin 3, ∀ y ∈ dtW s, cpdC j (cpdC d Gc) y = (cpd j (cpd d G) y : ℂ) := fun j =>
    cpdC_ofReal_on hW (cpd_contDiffOn' hW hGs d) R1 j
  have R3 : ∀ j k : Fin 3, ∀ y ∈ dtW s,
      cpdC k (cpdC j (cpdC d Gc)) y = (cpd k (cpd j (cpd d G)) y : ℂ) := fun j k =>
    cpdC_ofReal_on hW (cpd_contDiffOn' hW (cpd_contDiffOn' hW hGs d) j) (R2 j) k
  rw [R1 x hx, R2 0 x hx, R3 1 1 x hx, R3 2 2 x hx]
  have hheat := dtG_heat_d hH d x hx
  have hheatC : ((cpd 0 (cpd d G) x : ℝ) : ℂ) + (ν : ℂ) * (((cpd 1 (cpd 1 (cpd d G)) x : ℝ) : ℂ) +
      ((cpd 2 (cpd 2 (cpd d G)) x : ℝ) : ℂ)) = 0 := by
    exact_mod_cast hheat
  have hal := cpow_alg μ χ x.1 (hpos x hx) (hχd _)
  have hRHS : cpdC d (fun z => ((H (s - z.1, z.2) : ℝ) : ℂ)) x = (cpd d G x : ℂ) := by
    rw [← R1 x hx]; rfl
  rw [hRHS]
  have hax : a x.1 = (x.1 : ℂ) ^ (μ - 1) * (χ x.1 : ℂ) := rfl
  rw [← hax] at hal
  linear_combination (cpd d G x : ℂ) * hal - (x.1 : ℂ) * a x.1 * hheatC

theorem DualHeatIdentity_proof : UnforcedLeray.Short.IIb.DualHeatIdentity := by
  intro c ν μ H s r' χ hc hν hs hH hχ x i
  obtain ⟨hχs, hχc, hχt⟩ := hχ
  by_cases hx : x.1 ∈ tsupport χ
  · have hxW : x ∈ dtW s := ⟨hχt hx, trivial⟩
    fin_cases i
    · have := dual_core μ hH hχs 2 (by simp [cdir]) x hxW
      exact this
    · have := dual_core μ hH hχs 1 (by simp [cdir]) x hxW
      have hperp : perpC (fun z : Coord => ((H (s - z.1, z.2) : ℝ) : ℂ)) x 1 =
          -cpdC 1 (fun z : Coord => ((H (s - z.1, z.2) : ℝ) : ℂ)) x := rfl
      show flatTransposeC ν μ (perpC (dualPsiInf μ χ H s)) x 1 =
        -(((x.1 : ℂ) ^ μ) * ((deriv χ x.1 : ℝ) : ℂ) *
          perpC (fun z : Coord => ((H (s - z.1, z.2) : ℝ) : ℂ)) x 1)
      rw [hperp]
      have e : flatTransposeC ν μ (perpC (dualPsiInf μ χ H s)) x 1 =
          -((μ - 1) * cpdC 1 (dualPsiInf μ χ H s) x -
            (x.1 : ℂ) * cpdC 0 (cpdC 1 (dualPsiInf μ χ H s)) x -
            (ν : ℂ) * (x.1 : ℂ) * (cpdC 1 (cpdC 1 (cpdC 1 (dualPsiInf μ χ H s))) x +
              cpdC 2 (cpdC 2 (cpdC 1 (dualPsiInf μ χ H s))) x)) := by
        show (μ - 1) * (-cpdC 1 (dualPsiInf μ χ H s) x) -
          (x.1 : ℂ) * cpdC 0 (fun y => -cpdC 1 (dualPsiInf μ χ H s) y) x -
          (ν : ℂ) * (x.1 : ℂ) * (cpdC 1 (fun y => cpdC 1 (fun z => -cpdC 1 (dualPsiInf μ χ H s) z) y) x +
            cpdC 2 (fun y => cpdC 2 (fun z => -cpdC 1 (dualPsiInf μ χ H s) z) y) x) = _
        simp only [cpdC_neg']
        ring
      rw [e, this]; ring
  · have hV : IsOpen ((tsupport χ)ᶜ ×ˢ (univ : Set (ℝ × ℝ))) :=
      (isClosed_tsupport χ).isOpen_compl.prod isOpen_univ
    have hxV : x ∈ (tsupport χ)ᶜ ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hx, trivial⟩
    have hψ0 : ∀ y ∈ (tsupport χ)ᶜ ×ˢ (univ : Set (ℝ × ℝ)), dualPsiInf μ χ H s y = 0 := by
      intro y hy
      have : χ y.1 = 0 := image_eq_zero_of_notMem_tsupport hy.1
      simp [dualPsiInf, this]
    have hΨ : ∀ y ∈ (tsupport χ)ᶜ ×ˢ (univ : Set (ℝ × ℝ)), ∀ i, perpC (dualPsiInf μ χ H s) y i = 0 := by
      intro y hy i
      have c1 := cpdC_zero_on' hV hψ0 1 y hy
      have c2 := cpdC_zero_on' hV hψ0 2 y hy
      fin_cases i <;> simp [perpC, c1, c2]
    rw [flatTransposeC_zero_on hV ν μ _ hΨ x hxV i, deriv_of_notMem_tsupport hx]
    simp

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.DualHeatIdentity_proof
