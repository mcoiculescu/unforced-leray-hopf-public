import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSobolev.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/7`: assembly of `TimeJetsSTSobolev` from the leaves of `Defs.lean`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Plain integral identities give the one-letter weak derivative for the test domain of the slab. -/
theorem stWeakDeriv_of_identity {t s : ℝ} {v : ℝ × (ℝ × ℝ)} {G G' : ℝ × (ℝ × ℝ) → ℂ}
    (h : STStepIdentity (stSlab t s) v G G') :
    UnforcedLeray.Sob.HasWeakDeriv
      (stDomain (stSlab t s) (isOpen_Ioo.prod isOpen_univ)) [v] G G' := by
  have hU : IsOpen (stSlab t s) := isOpen_Ioo.prod isOpen_univ
  have hmeas : MeasurableSet (stSlab t s) := hU.measurableSet
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  all_goals
    obtain ⟨h1, h2, h3⟩ := h φ hφ.1 hφ.2.1 hφ.2.2
  · have e : (fun x => UnforcedLeray.Sob.iterDirDeriv [v] φ x • G x) =
        fun p => fderiv ℝ φ p v • G p := by
      funext x; simp [UnforcedLeray.Sob.iterDirDeriv]
    show Integrable _ (volume.restrict (stSlab t s))
    rw [e]
    exact h1.integrableOn
  · show Integrable _ (volume.restrict (stSlab t s))
    exact h2.integrableOn
  · have e : (fun x => UnforcedLeray.Sob.iterDirDeriv [v] φ x • G x) =
        fun p => fderiv ℝ φ p v • G p := by
      funext x; simp [UnforcedLeray.Sob.iterDirDeriv]
    show ∫ x, UnforcedLeray.Sob.iterDirDeriv [v] φ x • G x ∂(volume.restrict (stSlab t s)) =
      (-1 : ℝ) ^ [v].length • ∫ x, φ x • G' x ∂(volume.restrict (stSlab t s))
    rw [e]
    have z1 : ∫ p, fderiv ℝ φ p v • G p ∂(volume.restrict (stSlab t s)) =
        ∫ p, fderiv ℝ φ p v • G p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      have : fderiv ℝ φ p v = 0 := by
        by_contra hne
        exact hp (hφ.2.2 ((tsupport_fderiv_apply_subset ℝ v)
          (subset_tsupport _ (Function.mem_support.mpr hne))))
      simp [this]
    have z2 : ∫ p, φ p • G' p ∂(volume.restrict (stSlab t s)) = ∫ p, φ p • G' p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      have : φ p = 0 := by
        by_contra hne
        exact hp (hφ.2.2 (subset_tsupport _ (Function.mem_support.mpr hne)))
      simp [this]
    rw [z1, z2, h3]
    simp

/-- The zero-letter weak derivative of an `L²_loc` function is itself. -/
theorem stWeakDeriv_nil {t s : ℝ} {G : ℝ × (ℝ × ℝ) → ℂ} (hG : STLocL2 t s G) :
    UnforcedLeray.Sob.HasWeakDeriv
      (stDomain (stSlab t s) (isOpen_Ioo.prod isOpen_univ)) [] G G := by
  have hU : IsOpen (stSlab t s) := isOpen_Ioo.prod isOpen_univ
  have hint : ∀ φ : ℝ × (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ stSlab t s →
      Integrable (fun x => φ x • G x) (volume.restrict (stSlab t s)) := by
    intro φ h1 h2 h3
    have hK : IsCompact (tsupport φ) := h2.isCompact
    have hGK : MemLp G 2 (volume.restrict (tsupport φ)) := hG _ hK h3
    have : Fact (volume (tsupport φ) < ⊤) := ⟨hK.measure_lt_top⟩
    have hI : Integrable G (volume.restrict (tsupport φ)) := hGK.integrable one_le_two
    obtain ⟨C, hC⟩ := h1.continuous.bounded_above_of_compact_support h2
    have hI2 : IntegrableOn (fun x => φ x • G x) (tsupport φ) :=
      hI.bdd_smul C h1.continuous.aestronglyMeasurable (Eventually.of_forall hC)
    refine IntegrableOn.of_forall_diff_eq_zero hI2 hU.measurableSet fun x hx => ?_
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx.2
    simp [this]
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · show Integrable _ (volume.restrict (stSlab t s))
    simpa using hint φ hφ.1 hφ.2.1 hφ.2.2
  · show Integrable _ (volume.restrict (stSlab t s))
    exact hint φ hφ.1 hφ.2.1 hφ.2.2
  · simp


/-- A jointly measurable version of an `X_{-m,c}`-continuous path of `c`-periodic functions, equal
to the slice Lebesgue-almost everywhere for every `r` (`MeasPathVersion`, `MeasPlaneVersion`). -/
theorem measVersion_of (h7a : MeasPathVersion) (h7b : MeasPlaneVersion) (c m t s : ℝ)
    (f : ℝ → ℝ × ℝ → ℂ) (hc : 0 < c)
    (hper : ∀ r ∈ Ioo t s, Periodic1 c (f r) ∧ MemLp (f r) 2 (B0579.cellMeasure c (-m)))
    (hcont : ∀ r ∈ Ioo t s,
      Tendsto (fun r' => xNorm c (-m) (f r' - f r)) (𝓝[Ioo t s] r) (𝓝 0)) :
    ∃ G : ℝ × (ℝ × ℝ) → ℂ, Measurable G ∧
      ∀ r ∈ Ioo t s, (fun x => G (r, x)) =ᵐ[volume] f r := by
  haveI : SigmaFinite (B0579.cellMeasure c (-m)) := by
    unfold B0579.cellMeasure; infer_instance
  obtain ⟨F, hFm, hF⟩ := h7a (B0579.cellMeasure c (-m)) t s f (fun r hr => (hper r hr).2) hcont
  exact h7b c m t s f F hc hFm (fun r hr => (hper r hr).1) hF

/-- The test domain of the slab `(t, s) × ℝ²`. -/
abbrev stDom (t s : ℝ) : UnforcedLeray.Sob.TestDomain (ℝ × (ℝ × ℝ)) 3 :=
  stDomain (stSlab t s) (isOpen_Ioo.prod isOpen_univ)

/-- **`TimeJetsSTSobolev` from the leaves** (SP 3060-3061): coherent jets (`CohJetsExists`), jointly
measurable versions `G j w` of the fields `D j · w` (`MeasPathVersion`, `MeasPlaneVersion`),
`L²_loc` (`STLocL2Of`), the one-letter identities (`STSpaceIdentity` for `x`-letters,
`STTimeIdentity` for the age letter on `w = []`, extended to every `w` by `perm`/`append`/
`of_append`), and induction on the word. -/
theorem timeJetsSTSobolev_of (hCoh : CohJetsExists) (h7a : MeasPathVersion)
    (h7b : MeasPlaneVersion) (hL2 : STLocL2Of) (hT : STTimeIdentity) (hS : STSpaceIdentity) :
    TimeJetsSTSobolev := by
  intro c m t s Φ hc hts hJ
  obtain ⟨D, hD⟩ := hCoh c m t s Φ hc hJ
  have hper : ∀ (j : ℕ) (w : List (Fin 2)), ∀ r ∈ Ioo t s,
      Periodic1 c (D j r w) ∧ MemLp (D j r w) 2 (B0579.cellMeasure c (-m)) := fun j w r hr =>
    ⟨fun x => (hD.jet j w.length r hr).periodic w le_rfl x,
      (hD.jet j w.length r hr).memX w le_rfl⟩
  have hG : ∀ (j : ℕ) (w : List (Fin 2)), ∃ G : ℝ × (ℝ × ℝ) → ℂ, Measurable G ∧
      ∀ r ∈ Ioo t s, (fun x => G (r, x)) =ᵐ[volume] D j r w := fun j w =>
    measVersion_of h7a h7b c m t s (fun r => D j r w) hc (hper j w) (hD.cont j w)
  choose G hGm hGe using hG
  have hGL : ∀ (j : ℕ) (w : List (Fin 2)), STLocL2 t s (G j w) := fun j w =>
    hL2 c m t s (fun r => D j r w) (G j w) hc hts (hper j w) (hD.cont j w) (hGm j w) (hGe j w)
  have hsp : ∀ (j : ℕ) (w : List (Fin 2)) (i : Fin 2),
      UnforcedLeray.Sob.HasWeakDeriv (stDom t s) [stDir i.succ] (G j w) (G j (i :: w)) := by
    intro j w i
    refine stWeakDeriv_of_identity (hS c m t s i (fun r => D j r w) (fun r => D j r (i :: w))
      (G j w) (G j (i :: w)) hc hts ?_ (hGm j w) (hGm j (i :: w)) (hGL j w) (hGL j (i :: w))
      (hGe j w) (hGe j (i :: w)))
    intro r hr
    exact ⟨(hper j w r hr).1, (hper j w r hr).2, (hper j (i :: w) r hr).1,
      (hper j (i :: w) r hr).2, (hD.jet j (w.length + 1) r hr).deriv i w (Nat.lt_succ_self _)⟩
  have hbase : ∀ (j : ℕ), ∀ r ∈ Ioo t s,
      (fun x => G j [] (r, x)) =ᵐ[volume] Φ j r := fun j r hr => by
    have := hGe j [] r hr
    rwa [(hD.jet j 0 r hr).base] at this
  have ht0 : ∀ j : ℕ,
      UnforcedLeray.Sob.HasWeakDeriv (stDom t s) [stDir 0] (G j []) (G (j + 1) []) := fun j =>
    stWeakDeriv_of_identity (hT c m t s Φ j (G j []) (G (j + 1) []) hc hts hJ (hGm j [])
      (hGm (j + 1) []) (hGL j []) (hGL (j + 1) []) (hbase j) (hbase (j + 1)))
  have hchain : ∀ (j : ℕ) (w : List (Fin 2)), UnforcedLeray.Sob.HasWeakDeriv (stDom t s)
      (w.map fun i => stDir i.succ) (G j []) (G j w) := by
    intro j w
    induction w with
    | nil => exact stWeakDeriv_nil (hGL j [])
    | cons i w ih =>
      have h := ih.append (hsp j w i)
      exact UnforcedLeray.Sob.HasWeakDeriv.perm (List.perm_append_singleton _ _) h
  have htw : ∀ (j : ℕ) (w : List (Fin 2)),
      UnforcedLeray.Sob.HasWeakDeriv (stDom t s) [stDir 0] (G j w) (G (j + 1) w) := by
    intro j w
    have hb := (ht0 j).append (hchain (j + 1) w)
    have hb' := UnforcedLeray.Sob.HasWeakDeriv.perm List.perm_append_comm hb
    exact (hchain j w).of_append hb'
  have hlet : ∀ (a : Fin 3) (j : ℕ) (w : List (Fin 2)), ∃ (j' : ℕ) (w' : List (Fin 2)),
      UnforcedLeray.Sob.HasWeakDeriv (stDom t s) [stDir a] (G j w) (G j' w') := by
    intro a j w
    induction a using Fin.cases with
    | zero => exact ⟨j + 1, w, htw j w⟩
    | succ i => exact ⟨j, i :: w, hsp j w i⟩
  have hword : ∀ (l : List (Fin 3)) (j : ℕ) (w : List (Fin 2)), ∃ (j' : ℕ) (w' : List (Fin 2)),
      UnforcedLeray.Sob.HasWeakDeriv (stDom t s) (l.map stDir) (G j w) (G j' w') := by
    intro l
    induction l with
    | nil => intro j w; exact ⟨j, w, stWeakDeriv_nil (hGL j w)⟩
    | cons a l ih =>
      intro j w
      obtain ⟨j1, w1, h1⟩ := hlet a j w
      obtain ⟨j2, w2, h2⟩ := ih j1 w1
      exact ⟨j2, w2, h1.append h2⟩
  refine ⟨G 0 [], hbase 0, hGL 0 [], fun l => ?_⟩
  obtain ⟨j', w', h⟩ := hword l 0 []
  exact ⟨G j' w', hGL j' w', h⟩

end UnforcedLeray.Short.IIIa
