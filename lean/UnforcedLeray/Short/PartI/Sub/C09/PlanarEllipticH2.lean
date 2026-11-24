import UnforcedLeray.Short.PartI.Sub.C09.PlanarEllipticH2.Bridge
import UnforcedLeray.Short.PartI.Sub.C09.PlanarEllipticH2.Fourier

/-!


Source of record: `the November 2 reference manuscript`, lines 1134-1143
("elliptic regularity `‖Ψ‖_{H²} ≤ C(‖ΔΨ‖₂ + ‖Ψ‖₂)`").

`PlanarEllipticH2` (in `Sub/C09.lean`) is proved here by transferring `Lib/SobolevC/Elliptic.lean`
(`ellipticH2`, `IsWeakLaplacian`, the Fourier bounds) from `Eucl 2` to `ℝ × ℝ` along `toPlane`.

Helpers (folder `Sub/C09/PlanarEllipticH2/`):
* `Lap`: `weakLap_toPlane` (`WeakLapOn univ u g` gives `IsWeakLaplacian (u ∘ toPlane) (g ∘ toPlane)`),
  `iterD_post_clm`;
* `Tests`: `hasWeakDeriv_complex_test` (real `HasWeakDeriv` tests extended to complex tests);
* `Bridge`: `planar_bridge` (components of `W^{2,2}` are planar weak derivatives);
* `Fourier`: `firstOrder_bound` (`∑_i ∫|∂_i u|² ≤ 2π²(‖u‖² + ‖g‖²)` by Plancherel).

The multi-indices of order `≤ 2` are `(0,0)`, `(1,0)`, `(0,1)`, `(2,0)`, `(1,1)`, `(0,2)`;
`(0,0)` is the field itself, `(1,0)`, `(0,1)` are first derivatives, and the three second-order
entries are bounded by `∑_{i,j} ‖∂_i∂_j u‖² = ‖Δu‖²` (`ellipticH2`).  The constant is `C = 1 + 2π²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Sob

/-- The component word for each multi-index of order `≤ 2`. -/
def aOf (β : ℕ × ℕ) : Idx 2 2 :=
  if β = (1, 0) then alphaFst 0
  else if β = (0, 1) then alphaFst 1
  else if β = (2, 0) then idx2 0 0
  else if β = (1, 1) then idx2 0 1
  else if β = (0, 2) then idx2 1 1
  else Idx.zero

theorem multiIdx_two :
    UnforcedLeray.PlanarBS.Sob.multiIdx 2 = {(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)} := by
  decide

/-- The weak Laplacian identity is invariant under almost-everywhere changes of its fields. -/
theorem isWeakLaplacian_congr_ae {f f' g g' : Eucl 2 → ℂ}
    (h : UnforcedLeray.Sob.IsWeakLaplacian f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    UnforcedLeray.Sob.IsWeakLaplacian f' g' := by
  intro φ hφ hc
  have e1 : ∫ x, UnforcedLeray.Sob.lapl φ x • f' x = ∫ x, UnforcedLeray.Sob.lapl φ x • f x :=
    integral_congr_ae (hf.mono fun x hx => by dsimp only; rw [hx])
  have e2 : ∫ x, φ x • g' x = ∫ x, φ x • g x :=
    integral_congr_ae (hg.mono fun x hx => by dsimp only; rw [hx])
  rw [e1, e2]
  exact h φ hφ hc

theorem aOf_00 : aOf (0, 0) = Idx.zero := by simp [aOf]
theorem aOf_10 : aOf (1, 0) = alphaFst 0 := by simp [aOf]
theorem aOf_01 : aOf (0, 1) = alphaFst 1 := by simp [aOf]
theorem aOf_20 : aOf (2, 0) = idx2 0 0 := by simp [aOf]
theorem aOf_11 : aOf (1, 1) = idx2 0 1 := by simp [aOf]
theorem aOf_02 : aOf (0, 2) = idx2 1 1 := by simp [aOf]

theorem map_word_00 :
    ((wholeSpace 2).word (Idx.zero : Idx 2 2)).map toPlane =
      UnforcedLeray.B0121.pdListR (0, 0) := by
  simp [UnforcedLeray.B0121.pdListR]

theorem map_word_10 :
    ((wholeSpace 2).word (alphaFst 0)).map toPlane = UnforcedLeray.B0121.pdListR (1, 0) := by
  rw [word_alphaFst]
  simp [UnforcedLeray.B0121.pdListR, toPlane_e, planarH2_ev_eq_cylDir]

theorem map_word_01 :
    ((wholeSpace 2).word (alphaFst 1)).map toPlane = UnforcedLeray.B0121.pdListR (0, 1) := by
  rw [word_alphaFst]
  simp [UnforcedLeray.B0121.pdListR, toPlane_e, planarH2_ev_eq_cylDir]

theorem map_word_20 :
    ((wholeSpace 2).word (idx2 0 0)).map toPlane = UnforcedLeray.B0121.pdListR (2, 0) := by
  rw [word_idx2]
  simp [UnforcedLeray.B0121.pdListR, toPlane_e, planarH2_ev_eq_cylDir]

theorem map_word_11 :
    ((wholeSpace 2).word (idx2 0 1)).map toPlane = UnforcedLeray.B0121.pdListR (1, 1) := by
  rw [word_idx2]
  simp [UnforcedLeray.B0121.pdListR, toPlane_e, planarH2_ev_eq_cylDir]

theorem map_word_02 :
    ((wholeSpace 2).word (idx2 1 1)).map toPlane = UnforcedLeray.B0121.pdListR (0, 2) := by
  rw [word_idx2]
  simp [UnforcedLeray.B0121.pdListR, toPlane_e, planarH2_ev_eq_cylDir]

/-- Change of variables along `toPlane.symm`. -/
theorem integral_comp_toPlane_symm (G : Eucl 2 → ℝ) :
    ∫ z, G (toPlane.symm z) = ∫ y, G y :=
  measurePreserving_toPlane_symm.integral_comp measurableEmbedding_toPlane_symm G

/-- **`PartI:PlanarEllipticH2`** (source lines 1141-1142): `H²` regularity on `ℝ²`. -/
theorem planarEllipticH2 : PlanarEllipticH2 := by
  refine ⟨1 + 2 * π ^ 2, fun u g hu hg h => ?_⟩
  -- transfer to `Eucl 2`
  have hfE : MemLp (fun y : Eucl 2 => u (toPlane y)) 2 volume :=
    hu.comp_measurePreserving measurePreserving_toPlane
  have hgE : MemLp (fun y : Eucl 2 => g (toPlane y)) 2 volume :=
    hg.comp_measurePreserving measurePreserving_toPlane
  set FLp : Lp ℂ 2 (volume : Measure (Eucl 2)) := hfE.toLp _ with hFLp
  set GLp : Lp ℂ 2 (volume : Measure (Eucl 2)) := hgE.toLp _ with hGLp
  have hFLae : (FLp : Eucl 2 → ℂ) =ᵐ[volume] fun y => u (toPlane y) := hfE.coeFn_toLp
  have hGLae : (GLp : Eucl 2 → ℂ) =ᵐ[volume] fun y => g (toPlane y) := hgE.coeFn_toLp
  have hIW : IsWeakLaplacian (FLp : Eucl 2 → ℂ) (GLp : Eucl 2 → ℂ) :=
    isWeakLaplacian_congr_ae (weakLap_toPlane h) hFLae.symm hGLae.symm
  obtain ⟨x, hx, hsum⟩ := ellipticH2 hIW
  have hxu : toVol (W.value (wholeSpace 2) 1 ℂ ℂ 2 2 x) =ᵐ[volume] fun y => u (toPlane y) := by
    rw [hx]
    exact hFLae
  -- the candidate derivatives on `ℝ × ℝ`
  let v : ℕ × ℕ → ℝ × ℝ → ℂ := fun β z =>
    (toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (aOf β) x) : Eucl 2 → ℂ) (toPlane.symm z)
  have hmem : ∀ β, MemLp (v β) 2 volume := fun β =>
    (Lp.memLp _).comp_measurePreserving measurePreserving_toPlane_symm
  refine ⟨v, ?_, ?_⟩
  · intro β hβ
    rw [multiIdx_two] at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl
    · have hb := planar_bridge x hxu Idx.zero map_word_00
      rw [← aOf_00] at hb
      exact ⟨hmem _, hb⟩
    · have hb := planar_bridge x hxu (alphaFst 0) map_word_10
      rw [← aOf_10] at hb
      exact ⟨hmem _, hb⟩
    · have hb := planar_bridge x hxu (alphaFst 1) map_word_01
      rw [← aOf_01] at hb
      exact ⟨hmem _, hb⟩
    · have hb := planar_bridge x hxu (idx2 0 0) map_word_20
      rw [← aOf_20] at hb
      exact ⟨hmem _, hb⟩
    · have hb := planar_bridge x hxu (idx2 0 1) map_word_11
      rw [← aOf_11] at hb
      exact ⟨hmem _, hb⟩
    · have hb := planar_bridge x hxu (idx2 1 1) map_word_02
      rw [← aOf_02] at hb
      exact ⟨hmem _, hb⟩
  · -- the bound: the sum over `multiIdx 2` as six explicit terms
    rw [multiIdx_two, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have e : ∀ β, ∫ z, ‖v β z‖ ^ 2 =
        ∫ y, ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (aOf β) x) : Eucl 2 → ℂ) y‖ ^ 2 :=
      fun β => integral_comp_toPlane_symm
        (fun y => ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (aOf β) x) : Eucl 2 → ℂ) y‖ ^ 2)
    rw [e, e, e, e, e, e]
    simp only [aOf_00, aOf_10, aOf_01, aOf_20, aOf_11, aOf_02]
    -- the zeroth-order term is the field itself
    have h00 : ∫ y, ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 Idx.zero x) : Eucl 2 → ℂ) y‖ ^ 2 =
        ‖FLp‖ ^ 2 := by
      rw [W.deriv_zero, hx, integral_sq_norm_Lp']
    -- the first-order terms
    have hfo := firstOrder_bound x hx hIW
    rw [Fin.sum_univ_two] at hfo
    -- the second-order terms
    have hW2 : ∀ i j : Fin 2,
        ∫ y, ‖(toVol (W.deriv (wholeSpace 2) 1 ℂ ℂ 2 2 (idx2 i j) x) : Eucl 2 → ℂ) y‖ ^ 2 =
          ‖W.second x i j‖ ^ 2 := by
      intro i j
      rw [integral_sq_norm_Lp', norm_toVol]
      rfl
    have hsec := hsum
    simp only [Fin.sum_univ_two] at hsec
    have hsq10 : 0 ≤ ‖W.second x 1 0‖ ^ 2 := sq_nonneg _
    -- the field and the right-hand side
    have hA : ∫ z, ‖u z‖ ^ 2 = ‖FLp‖ ^ 2 := by
      calc ∫ z, ‖u z‖ ^ 2 = ∫ y, ‖u (toPlane y)‖ ^ 2 :=
            (measurePreserving_toPlane.integral_comp measurableEmbedding_toPlane
              (fun z => ‖u z‖ ^ 2)).symm
        _ = ∫ y, ‖(FLp : Eucl 2 → ℂ) y‖ ^ 2 :=
            integral_congr_ae (hFLae.mono fun y hy => by dsimp only; rw [hy])
        _ = ‖FLp‖ ^ 2 := integral_sq_norm_Lp' FLp
    have hB : ∫ z, ‖g z‖ ^ 2 = ‖GLp‖ ^ 2 := by
      calc ∫ z, ‖g z‖ ^ 2 = ∫ y, ‖g (toPlane y)‖ ^ 2 :=
            (measurePreserving_toPlane.integral_comp measurableEmbedding_toPlane
              (fun z => ‖g z‖ ^ 2)).symm
        _ = ∫ y, ‖(GLp : Eucl 2 → ℂ) y‖ ^ 2 :=
            integral_congr_ae (hGLae.mono fun y hy => by dsimp only; rw [hy])
        _ = ‖GLp‖ ^ 2 := integral_sq_norm_Lp' GLp
    have h20 := hW2 0 0
    have h11 := hW2 0 1
    have h02 := hW2 1 1
    rw [hA, hB, h00]
    have key : (1 + 2 * π ^ 2) * (‖FLp‖ ^ 2 + ‖GLp‖ ^ 2) =
        ‖FLp‖ ^ 2 + 2 * π ^ 2 * (‖FLp‖ ^ 2 + ‖GLp‖ ^ 2) + ‖GLp‖ ^ 2 := by ring
    linarith [hfo, hsec, hsq10, key, h20, h11, h02]

end UnforcedLeray.Short.PartI
