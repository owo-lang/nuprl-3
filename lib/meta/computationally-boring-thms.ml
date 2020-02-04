% If the value on the rhs is made into one big list, then Lisp will get a very
bad error: "attempt to make a stack frame larger than 256 words".  Resuming from 
this error will crash the machine.  %

let computationally_boring_thms = 
[`some_omega_members`; `omega_cases`; `omega_cases_2`; `U_members`; `U_cumulativity`;
`U1_contained_in_Ui`; `and_wf`; `squash_wf`; `prod_wf`; `set_wf`; `imp_wf`; `fun_wf`; `or_wf`;
`list_wf`; `eq_wf`; `tight_subst`; `if_null_wf`; `if_null_char`; `if_null_wf_2`; 
`cons_of_append`; `append_assoc`; `append_to_nil`;
`all_elements_mono`; `all_elements_of_append`;
`all_elements_of_cons`; `append_of_all_elements`; `cons_of_all_elements`;
`some_element_mono`; `map_on_empty`; `map_on_nonempty`;
`it_fun_base`; `it_fun_unroll`;
`it_fun_on_cons_base`; `it_fun_on_cons_unroll`; `length_of_tl`;
`length_of_map`; `not_null_iff_length`; `com_on_empty`; `com_on_nonempty`;
`some_element_mono_wrt_sublist`; `sublist_refl`; `sublist_trans`;
`List_inclusion`; `List_inclusion_2`; `List_inclusion_3`; 
`list_subset_membership`;
`eq_lists_if_eq_in_superset`; 
`eos_eq_reln`] @
[`fun_eq_eq_reln`; 
`prod_eq_eq_reln`; 
`Set1_contained_in_Set`; `Set_contained_in_SET`;
`SET_eq_if_Set_eq`;
`prod_of_list_base`; `prod_of_list_unroll`; `unroll_tos_on_prod_of_list`;
`roll_tos_on_prod_of_list`; 
`alist_ap_on_cons`; `sub_alist_of_cons`; `cons_sub_alist`;
`sub_alist_refl`; `sub_alist_trans`;
`lemma_for_alist_ap_mono_lemma`; `alist_ap_mono_lemma`;
`mtype_dom_i_atoms`; `mtype_range_i`; `TEnvVal_contained_in_TEnvAp_i`;
`TEnvAp_i_eq_if_TEnvVal_eq`; `trivial_sub_tenv`; `tenv_ap_i_mono`;
`type_atom@_mono`; `type_atom_mono`; `AtomicMType_i_mono`; `all_type_atoms@_mono`;
`all_type_atoms_mono`; `MType_i_mono`; `type_atom_val_i_mono`;
`type_atom_val_i_on_Prop`; `mtype_dom_val_i_mono`; 
`mtype_val_i_mono`; `mtype_val_i_type_mono`; `mtype_val_i_char`; `type_atom_val_smallish`;
`type_atom_val_eq_small`; `type_atom_val_i_small_type`; `eos_on_SmallEqSET`;
`SmallEqSET_contained_in_SET`; `Set_contained_in_SmallEqSET`; 
`Prop_small_type`; `tenv_alist_ap_small`; `tenv_ap_i_small_type`;
`TEnvVal_contained_in_SmallTEnvAp_i`; `tenv_ap_i_small_mono`; `val_triv_pred_i_mono`; `val_triv_pred_i_mono_2`] @

[`val_semi_triv_pred_i_mono`; `val_semi_triv_pred_i_mono_2`; 
`val_full_injection_i_mono`; `val_full_injection_i_mono_2`; `val_kind_i_mono`;
`val_kind_i_mono_2`; `FEnvVal_i_mono`; `FEnvVal_i_mono_2`;
`FEnv_mono`; `FEnv_containment_lemma_2`; `FEnv_containment_lemma`; `mtype_dom_atoms`; `mtype_range`; 
`type_atom_val_small_type`; `mtype_val_char`; `fun_atom_char`; `constant_mfun_val`; 
`mfun_val_fun`; `mfun_val_ap`; `Int_in_AtomicMType`; `Prop_in_AtomicMType`;
`arg_tuple_typing`; `wf_fun_ap@_body`; `wf_i_pair@_body`;
`main_typing_lemma`; `term_list_val_in_mtype_dom`;
`mfun_if_wf_term@_1`; `mfun_if_wf_term@_2`; `wf_i_pair@_aux_lemma`; `mtype_pair`; `Term_containment_lemma`; 
`vals_in_mtypes_char`; `wf_fun_ap_aux_char`; `wf_fun_ap_char`; `wf_eq_ap_char`; `b_is_injection_char`; 
`wf_i_pair_aux_char`; `wf_i_pair_char`; `all_elements_mono_lemma`; `wf_term_lemma`; `wf_term_char`; 
`term_list_type_base`; `term_list_type_base_mem`; `term_list_type_unroll`;
`term_list_type_unroll_mem`; `FEnvVal_mono`; `MType_mono`;
`AtomicMType_mono`; `tenv_ap_mono`; `type_atom_val_mono`; `type_atom_val_small_mono`;
`type_atom_val_mem_mono`; `mtype_dom_val_mono`; `mtype_dom_val_mem_mono`; `mtype_val_mono`;
`mtype_val_mem_mono`; `bound_mono`; `fun_atom@_mono`; `fun_atom_mono`; `MFun_mono`; `fenv_ap_mono`;
`mtype_mono`; `mtype_val_on_mtype_mem_mono`; `mfun_val_mono`; `val_kind_mem_mono`;
`val_kind_mono`; `val_kind_pf_mono`; `is_injection_mono`; `is_triv_pred_mono`;
`is_semi_triv_pred_mono`; `Val_mono`; `val_member_eq_mono`; `val_member_mono`;
`vals_in_mtypes@_mono`; `term_mtype_mono`; `term_type_mono_lemma`; `val_eq_when_val_member`;
`List_inclusion_2_lemma`; `List_inclusion_3_lemma`; `arg_tuple_eq`; `constant_mfun_val_mono`;
`mfun_val_fun_mono`; `term_val_mono_lemma`; `and_all_elements`; `subset_if_all_elements`;
`wf_i_pair@_aux_mono_lemma`; `val_member_mono_2`; `wf_term@_mono`; `term_type_mono`]@

[`term_val_mono`; `term_list_type_mono`; `term_list_type_mem_mono`; `terms_val_mono`;
`appended_alist_ap`; `alist_values_char`; 
`sub_alist_of_append`; `sub_alist_char_2`; `sub_fenv_mono`;
`cst_if_sub_alist`; `append_to_sub_alist`; `append_lub_wrt_sub_alist`; `cst_alists_sym`;
`alist_cst_with_append`; `membership_of_FEnv_of_append`; `subenv_of_append`;
`cst_if_subenv`; `append_to_subenv`; `subenv_refl`; `subenv_trans`; `cst_envs_refl`;
`cst_fenvs_mono`; `cst_envs_sym`; `env_cst_with_append`; `append_env_list_wf_lemma`; `env_cst_with_list_append`;
`member_subenv`; `cst_alists_if_disjoint`; `all_elements_anti_mono`;
`member_cst`; `append_lub_wrt_subenv`; `sublist_of_cons`; `sublist_cst`; 
`sublist_if_subseq`; `subenv_of_add_constants`; `term_mtype_eval_lemma`;
`wf_term_eval_lemma`; `term_val_eval_lemma_1`; `term_val_eval_lemma_2`;
`all_elements_if_all_elements`; `subenv_of_append_list`; `subenv_of_append_list_lemma`;
`simple_val_member`; `eq_term_val_char`; `term_mtype_mono_2`;
`AtomicMType_eq_char`; `Term_mono`; `eq_term_val_mono`; `eq_types_when_eq_mtypes`;
`mem_when_eq_mtype`; `eos_of_eq_sets`; `eq_term_val_refl`; `eq_term_val_sym`; `eq_term_val_trans`;
`val_inv_triv`; `Rewrite_eq_i`; `Rewrite_char`;
`rewrite_THEN_wf_lemma`; `rewrite_ORELSE_wf_lemma`; `rewrite_Id_wf_lemma`;
`rewrite_letrec_wf_lemma`; `rewrite_Repeat_wf_lemma`; `vals_type_base`;
`vals_type_unroll`; `terms_vals_type`; `eq_types_if_eq_vals`;
`vals_val_base`; `vals_val_unroll`; `vals_val_fnl`;
`prod_of_list_base_mem`; `eq_term_val_when_val_member`; `length_when_vals_in_mtypes`; `vals_in_mtypes_unroll`;
`terms_val_mem`; `terms_val_unroll`; `fun_ap_arg_length`; `fun_aps_arg_length`;
`fun_ap_functionality_lemma`; `fun_ap_functionality_lemma_2`; `mfun_val_fnl`] @

[`fun_ap_functional`; `ifs_i`;
`fmap_success`; `fmap_char`; `ds_on_slet`; `slet_success`; `rewrite_Sub_on_fun_ap`;
`vals_in_mtypes_roll`; `val_member_when_eq_term_vals`; `vals_in_mtypes_on_eq_term_vals`;
`members_when_wf_eq_ap`; `eq_ap_fnl`; `inj_ap_eq_lemma`; `types_when_wf_i_pair`;
`wf_eq_ap_when_eq_term_val`; `rewrite_Sub_wf_lemma`; 
`fun_ap_functional_2`; `all_members_of_com`;
`com_all_elements`; `wf_i_pair_fnlty`; `wf_i_pair_injectiveness`; `inj_ap_eq_lemma_2`;
`inj_ap_when_wf_i_pair`; `i_pair_fnl`; `eq_true_when_eq_term_val`;
`rewrite_true_eq_wf_lemma`; `covering_subst_mono`; `subst_succeeds`;
`subst_base`; `subst_fails`; `subst_base_2`; `subst_on_fun_ap`; `subst_on_eq_ap`;
`subst_on_i_pair`; `subst_mono`; `limited_appended_subst`;
`complete_subst_on_fun_ap`; `complete_subst_on_eq_ap`;
`complete_subst_on_i_pair`; `full_subst_from_subst`;
`length_of_com`; `limited_subst_if_full`; `all_elements_elim`; `constant_char`;
`limited_subst_failure`; `full_subst_from_limited_subst`; 
`val_member_char_2`; `type_when_prop`; `eq_term_val_when_props`;
`trivial_env_append`; `trivially_cst_envs`; 
`terms_eq_in_mtype_sym`;
`terms_eq_in_mtype_sym_2`; `terms_eq_in_mtype_trans`; `terms_eq_in_mtype_trans_2`;
`m_bin_op_ap_wf`; `eq_terms_in_mtype_refl`; 
`m_bin_op_fnlty`; 
`m_monoid_mono`; `m_com_monoid_mono`; `eq_term_val_if_eq_terms_in_mtype`;
`rewrite_Progress_wf_lemma`; `rewrite_Try_wf_lemma`;
`triv_eq_pf_char`; `Int_cancellation`; `Int_cancellation_2`; `Q_plus_assoc`; `Q_plus_com`; 
`Q_mult_assoc`; `Q_mult_com`; `Q_additive_m_com_monoid`; `Q_multiplicative_m_com_monoid`; 
`Q_mult_over_plus`]
;; 