import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_349 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ (g H : Fin b) (u : Fin n), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → u ∉ I → (∃ w ∈ I, G.Adj u w) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro n b G PV RV PG RG OV OG val hP hR hval hout g H u hgH huP huR hloc I hI huI hw hH
  -- the output is false at I, since I is independent
  have hnoI : ¬ ((∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j) := by
    rw [hout I]
    rintro ⟨a, ha, c, hc, hac⟩
    exact hI a ha c hc hac
  -- the main claim: the P side of g is false at I
  have key : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) := by
    intro hPg
    -- adding u changes no gate
    have back : ∀ i : Fin b, val (insert u I) i → val I i := by
      intro i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        intro hi
        by_cases hiH : i = H
        · subst hiH
          exact hH
        rw [hval] at hi
        rw [hval]
        obtain ⟨h1, h2⟩ := hi
        -- the R side never reads u
        have hRside : (∃ v ∈ RV i, v ∈ I) ∨ ∃ j ∈ RG i, val I j := by
          rcases h2 with ⟨v, hv, hvX⟩ | ⟨j, hj, hjX⟩
          · left
            refine ⟨v, hv, ?_⟩
            rcases Finset.mem_insert.mp hvX with hvu | hvI
            · rw [hvu] at hv
              rcases hloc i (Or.inr hv) with h | h
              · rw [h] at hv
                exact absurd hv huR
              · exact absurd h hiH
            · exact hvI
          · exact Or.inr ⟨j, hj, ih j (hR i j hj) hjX⟩
        refine ⟨?_, hRside⟩
        by_cases hig : i = g
        · subst hig
          exact hPg
        rcases h1 with ⟨v, hv, hvX⟩ | ⟨j, hj, hjX⟩
        · left
          refine ⟨v, hv, ?_⟩
          rcases Finset.mem_insert.mp hvX with hvu | hvI
          · rw [hvu] at hv
            rcases hloc i (Or.inl hv) with h | h
            · exact absurd h hig
            · exact absurd h hiH
          · exact hvI
        · exact Or.inr ⟨j, hj, ih j (hP i j hj) hjX⟩
    -- yet the output must be true at insert u I
    obtain ⟨w, hwI, huw⟩ := hw
    have hX : (∃ v ∈ OV, v ∈ insert u I) ∨ ∃ j ∈ OG, val (insert u I) j := by
      rw [hout]
      exact ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, huw⟩
    rcases hX with ⟨v, hv, hvX⟩ | ⟨j, hj, hjX⟩
    · rcases Finset.mem_insert.mp hvX with rfl | hvI
      · -- u itself would be an output literal, but the singleton has no edge
        have hs : (∃ v' ∈ OV, v' ∈ ({v} : Finset (Fin n))) ∨ ∃ j ∈ OG, val {v} j :=
          Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
        rw [hout] at hs
        obtain ⟨a, ha, c, hc, hac⟩ := hs
        rw [Finset.mem_singleton] at ha hc
        subst ha hc
        exact G.irrefl hac
      · exact hnoI (Or.inl ⟨v, hv, hvI⟩)
    · exact hnoI (Or.inr ⟨j, hj, back j hjX⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hvI
    exact key (Or.inl ⟨v, hv, hvI⟩)
  · intro j hj hjI
    exact key (Or.inr ⟨j, hj, hjI⟩)
  · intro hHg
    exact key (Or.inr ⟨H, hHg, hH⟩)
