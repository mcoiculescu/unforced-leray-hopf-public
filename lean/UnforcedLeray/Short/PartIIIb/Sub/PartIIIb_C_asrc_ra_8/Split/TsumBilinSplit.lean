import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Defs

/-!
# `PartIII-b:C/asrc/ra/8/1/9` : leaf (D) `TsumBilinSplit`

Source of record: `the November 2 reference manuscript` (73 pages), 5026-5027
(the convection products `(ΣDb_j)(ΣV_k) + (ΣDV_k)(Σb_j)` split into the diagonal `j = k` and the
distinct-center terms `k ≠ j`).

Proof: the family `G(j,k) = Db_j(V_k) + DV_k(b_j)` on `ℤ × ℤ` is summable (product of summable
norms). Its total sum is `(ΣDb)(ΣV) + (ΣDV)(Σb)` by the fibre theorem `HasSum.prod_fiberwise`. Each
fibre `k ↦ G(j,k)` has sum `G(j,j) + Σ_{k≠j} G(j,k)`, so the fibre-sum family `j ↦ G(j,j) + H_j`
(with `H_j = Σ_{k≠j} G(j,k)`) has the same total sum. The diagonal `j ↦ G(j,j)` is summable
(injective reindexing of a summable family), hence so is `H`, and subtracting gives the claim.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The summand `G(j,k) = Db_j(V_k) + DV_k(b_j)` of the convection split, as a function on `ℤ × ℤ`. -/
def bkD_G (b V : ℤ → ℝ × ℝ) (Db DV : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)) (p : ℤ × ℤ) : ℝ × ℝ :=
  Db p.1 (V p.2) + DV p.2 (b p.1)

/-- Summability on `ℤ × ℤ` of `(j,k) ↦ L_j(v_k)` from summable operator and vector norms. -/
lemma bkD_summable_bil (L : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)) (v : ℤ → ℝ × ℝ)
    (hL : Summable fun j => ‖L j‖) (hv : Summable fun k => ‖v k‖) :
    Summable (fun p : ℤ × ℤ => L p.1 (v p.2)) := by
  have hL' : Summable fun j => ‖‖L j‖‖ := by simpa only [norm_norm] using hL
  have hv' : Summable fun k => ‖‖v k‖‖ := by simpa only [norm_norm] using hv
  refine Summable.of_norm_bounded (summable_mul_of_summable_norm hL' hv') (fun p => ?_)
  exact (L p.1).le_opNorm (v p.2)

/-- Summability on `ℤ × ℤ` of `(j,k) ↦ L_k(v_j)`, i.e. the first index feeds `v`. -/
lemma bkD_summable_bil_swap (L : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)) (v : ℤ → ℝ × ℝ)
    (hL : Summable fun j => ‖L j‖) (hv : Summable fun k => ‖v k‖) :
    Summable (fun p : ℤ × ℤ => L p.2 (v p.1)) := by
  have hL' : Summable fun j => ‖‖L j‖‖ := by simpa only [norm_norm] using hL
  have hv' : Summable fun k => ‖‖v k‖‖ := by simpa only [norm_norm] using hv
  refine Summable.of_norm_bounded (summable_mul_of_summable_norm hv' hL') (fun p => ?_)
  exact ((L p.2).le_opNorm (v p.1)).trans_eq (mul_comm _ _)

/-- The bilinear tsum identity `Σ_{(j,k)} L_j(v_k) = (ΣL)(Σv)`. -/
lemma bkD_tsum_bil (L : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)) (v : ℤ → ℝ × ℝ)
    (hL : Summable fun j => ‖L j‖) (hv : Summable fun k => ‖v k‖) :
    ∑' p : ℤ × ℤ, L p.1 (v p.2) = (∑' j, L j) (∑' k, v k) := by
  have hs := bkD_summable_bil L v hL hv
  have hLs : Summable L := hL.of_norm
  have hvs : Summable v := hv.of_norm
  have h1 : HasSum (fun j => L j (∑' k, v k)) (∑' p : ℤ × ℤ, L p.1 (v p.2)) :=
    hs.hasSum.prod_fiberwise (fun j => ContinuousLinearMap.hasSum (L j) hvs.hasSum)
  have h2 : HasSum (fun j => L j (∑' k, v k)) ((∑' j, L j) (∑' k, v k)) := by
    have := ContinuousLinearMap.hasSum (ContinuousLinearMap.apply ℝ (ℝ × ℝ) (∑' k, v k)) hLs.hasSum
    simpa using this
  exact h1.unique h2

/-- The swapped bilinear tsum identity `Σ_{(j,k)} L_k(v_j) = (ΣL)(Σv)`. -/
lemma bkD_tsum_bil_swap (L : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)) (v : ℤ → ℝ × ℝ)
    (hL : Summable fun j => ‖L j‖) (hv : Summable fun k => ‖v k‖) :
    ∑' p : ℤ × ℤ, L p.2 (v p.1) = (∑' j, L j) (∑' k, v k) := by
  rw [← bkD_tsum_bil L v hL hv]
  exact (Equiv.prodComm ℤ ℤ).tsum_eq (fun c => L c.1 (v c.2))

theorem tsumBilinSplit : TsumBilinSplit := by
  intro b V Db DV hb hV hDb hDV
  have hG1 : Summable (fun p : ℤ × ℤ => Db p.1 (V p.2)) := bkD_summable_bil Db V hDb hV
  have hG2 : Summable (fun p : ℤ × ℤ => DV p.2 (b p.1)) := bkD_summable_bil_swap DV b hDV hb
  have hGs : Summable (bkD_G b V Db DV) := hG1.add hG2
  have hGtot : ∑' p : ℤ × ℤ, bkD_G b V Db DV p
      = (∑' j, Db j) (∑' k, V k) + (∑' k, DV k) (∑' j, b j) := by
    rw [← bkD_tsum_bil Db V hDb hV, ← bkD_tsum_bil_swap DV b hDV hb]
    exact (hG1.hasSum.add hG2.hasSum).tsum_eq
  -- fibre over `j`: `k ↦ G(j,k)` has sum `G(j,j) + H_j`
  have hfib : ∀ j : ℤ, HasSum (fun k => bkD_G b V Db DV (j, k))
      (bkD_G b V Db DV (j, j) + ∑' k, if k = j then 0 else bkD_G b V Db DV (j, k)) := by
    intro j
    have hfiber : Summable (fun k => bkD_G b V Db DV (j, k)) := hGs.prod_factor j
    have hd : HasSum (fun k => if k = j then bkD_G b V Db DV (j, j) else 0)
        (bkD_G b V Db DV (j, j)) := hasSum_ite_eq j _
    have hoffs : Summable (fun k => if k = j then (0 : ℝ × ℝ) else bkD_G b V Db DV (j, k)) := by
      refine (hfiber.sub hd.summable).congr (fun k => ?_)
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    have hsum := hd.add hoffs.hasSum
    have hfun : (fun k => bkD_G b V Db DV (j, k)) = fun k =>
        (if k = j then bkD_G b V Db DV (j, j) else 0)
          + (if k = j then (0 : ℝ × ℝ) else bkD_G b V Db DV (j, k)) := by
      funext k
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    rw [hfun]
    exact hsum
  -- the fibre-sum family over `j`
  have hS' : HasSum (fun j => bkD_G b V Db DV (j, j)
      + ∑' k, if k = j then 0 else bkD_G b V Db DV (j, k))
      (∑' p : ℤ × ℤ, bkD_G b V Db DV p) :=
    hGs.hasSum.prod_fiberwise hfib
  -- the diagonal is summable
  have hinj : Function.Injective (fun j : ℤ => (j, j)) := fun a b h => congrArg Prod.fst h
  have hdiag : Summable (fun j : ℤ => bkD_G b V Db DV (j, j)) := hGs.comp_injective hinj
  -- the off-diagonal family is summable
  have hHs : Summable (fun j : ℤ => ∑' k, if k = j then 0 else bkD_G b V Db DV (j, k)) := by
    refine (hS'.summable.sub hdiag).congr (fun j => ?_)
    simp
  have hfinal := hS'.sub hHs.hasSum
  rw [hGtot] at hfinal
  have e : (fun j : ℤ => bkD_G b V Db DV (j, j)
      + (∑' k, if k = j then 0 else bkD_G b V Db DV (j, k))
      - ∑' k, if k = j then 0 else bkD_G b V Db DV (j, k))
      = fun j => Db j (V j) + DV j (b j) := by
    funext j
    exact add_sub_cancel_right _ _
  rw [e] at hfinal
  exact hfinal

end UnforcedLeray.Short.PartIIIb.Concrete
