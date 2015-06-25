DECLARE PLUGIN "pra_plugin"

let () = Mltop.add_known_plugin (fun () ->
  Flags.if_verbose Pp.ppnl Pp.(str "PRA plugin loaded."))
  "pra_plugin"
;;

open Glob_term
open Globnames
open Misctypes
open Evar_kinds
open Decl_kinds
open Names
open Proofview
open Pretyping
open Genarg
open Tacticals.New
open Term
open Vars
open Constrintern
open Constrextern

let constant dir s =
	Coqlib.gen_constant "QuoteTerm" dir s	

let my_constant s =
	let dir = make_dirpath (List.map id_of_string (List.rev ["pra"]))
	and id = id_of_string s in
	let sp = Libnames.make_path dir id in
	try
		Universes.constr_of_reference (Nametab.absolute_reference sp)
	with Not_found ->
		Errors.errorlabstrm "QuoteTerm" Pp.(str "cannot find" ++ Libnames.pr_path sp)

let rec quoteterm t: Term.constr =
	let coq_nat = constant ["Init";"Datatypes"] "nat"
	and coq_lt = constant ["Init";"Peano"] "lt"
	and coq_le = constant ["Init";"Peano"] "le"
	and coq_eq = constant ["Init";"Logic"] "eq"
	and coq_ge = constant ["Init";"Peano"] "ge"
	and coq_gt = constant ["Init";"Peano"] "gt"
	and coq_not = constant ["Init";"Logic"] "not"
	and coq_and = constant ["Init";"Logic"] "and"
	and coq_or = constant ["Init";"Logic"] "or"
	and coq_ex = constant ["Init";"Logic"] "ex"
	and coq_in = constant ["Lists";"List"] "In"
	and coq_succ = my_constant "Succ"
	and coq_z = constant ["ZArith";"BinInt"] "Z"
	and coq_zlt = constant ["ZArith";"BinInt"] "Zlt"
	and coq_zle = constant ["ZArith";"BinInt"] "Zle"
	and coq_zge = constant ["ZArith";"BinInt"] "Zge"
	and coq_zgt = constant ["ZArith";"BinInt"] "Zgt"
	and coq_prod = constant ["Init";"Datatypes"] "prod"
	and coq_f_all = my_constant "f_all"
	and coq_f_ex = my_constant "f_ex"
	and coq_f_lt = my_constant "f_lt"
	and coq_f_le = my_constant "f_le"
	and coq_f_eq = my_constant "f_eq"
	and coq_f_ge = my_constant "f_ge"
	and coq_f_gt = my_constant "f_gt"
	and coq_f_not = my_constant "f_not"
	and coq_f_and = my_constant "f_and"
	and coq_f_or = my_constant "f_or"
	and coq_f_imp = my_constant "f_imp"
	and coq_f_all_el = my_constant "f_all_el"
	and coq_f_ex_el = my_constant "f_ex_el"
	and coq_f_in = my_constant "f_in"
	and coq_f_zall = my_constant "f_zall"
	and coq_f_zex = my_constant "f_zex"
	and coq_f_zlt = my_constant "f_zlt"
	and coq_f_zle = my_constant "f_zle"
	and coq_f_zeq = my_constant "f_zeq"
	and coq_f_zge = my_constant "f_zge"
	and coq_f_zgt = my_constant "f_zgt"
	and coq_f_zall_el = my_constant "f_zall_el"
	and coq_f_zex_el = my_constant "f_zex_el"
	and coq_f_zin = my_constant "f_zin"
	and coq_f_succ = my_constant "f_succ"
	and coq_f_zsucc = my_constant "f_zsucc"
	and coq_f_p_in = my_constant "f_p_in"
	and coq_f_p_zin = my_constant "f_p_zin" in

	begin
		let quote_ex_nat l =
		try
			let x, t1, t2 = destLambda l in
			if isApp t2 then
				let f', a' = destApplication t2 in
				if eq_constr f' coq_and then
					if isApp (Array.get a' 0) then
						let f'', a'' = destApplication (Array.get a' 0) in
						if (eq_constr f'' coq_le) && (destRel (Array.get a'' 0) = 1) then
							mkApp (coq_f_ex, [| Array.get a'' 1; mkLambda (x, t1, quoteterm (Array.get a' 1)) |])
						else if (eq_constr f'' coq_in) && (destRel (Array.get a'' 1) = 1) then
							mkApp (coq_f_ex_el, [| Array.get a'' 2; mkLambda (x, t1, quoteterm (Array.get a' 1)) |])
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
		with
			Invalid_argument _ -> Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
	
		and quote_ex_z l =
		try
			let x, t1, t2 = destLambda l in
			if isApp t2 then
				let f0, a0 = destApplication t2 in
				if (eq_constr f0 coq_and) && (isApp (Array.get a0 0)) then
					let f1, a1 = destApplication (Array.get a0 0) in
					if (eq_constr f1 coq_and) && (isApp (Array.get a1 0)) && (isApp (Array.get a1 1)) then
						let f2a, a2a = destApplication (Array.get a1 0) and
						    f2b, a2b = destApplication (Array.get a1 1) in
						begin			
						if (eq_constr f2a coq_zgt) && (destRel (Array.get a2a 0) = 1) &&
						   (isConstruct (Array.get a2a 1)) &&
						   (eq_constr f2b coq_zle) && (destRel (Array.get a2b 0) = 1)  then
							 mkApp (coq_f_zex,	[| Array.get a2b 1; mkLambda (x, t1, quoteterm (Array.get a0 1)) |])
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
						end
					else if (eq_constr f1 coq_in) && (destRel (Array.get a1 1) = 1) then
						mkApp (coq_f_zex_el, [| Array.get a1 2; mkLambda (x, t1, quoteterm (Array.get a0 1)) |])
					else
            Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
				else
          Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
			else
        Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
		with
			Invalid_argument _ -> Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
	
		and quote_prod_nat i t1 t2 =
		let _, t3, t4 = (destProd t2) in
		if (isApp t3) then
			let f, a = (destApplication t3) in
			if (eq_constr f coq_le) && (Array.length a = 2) && (destRel (Array.get a 0) = 1) then
				mkApp (coq_f_all, [| Array.get a 1; mkLambda (i, t1, quoteterm (lift (-1) t4)) |])
			else if (eq_constr f coq_in) && (Array.length a = 3) && (destRel (Array.get a 1) = 1) then
				mkApp (coq_f_all_el, [| Array.get a 2; mkLambda (i, t1, quoteterm (lift (-1) t4)) |])
			else
        Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected: (x:nat) (le x A) -> B or (x: nat) (in l x) -> A")
		else
      Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected: (x:nat) (le x A) -> B or (x: nat) (in l x) -> A")
	
		and quote_prod_z i t1 t2 =
		let _, t3, t4 = (destProd t2) in
		if isApp t3 then
			let f, a = (destApplication t3) in
			if (eq_constr f coq_and) && (isApp (Array.get a 0)) && (isApp (Array.get a 1)) then
				let f1a, a1a = (destApplication (Array.get a 0)) and
		   			f1b, a1b = (destApplication (Array.get a 1)) in
				if (eq_constr f1a coq_zgt) && (destRel (Array.get a1a 0) = 1) &&
	   			 (eq_constr f1b coq_zle) && (destRel (Array.get a1b 0) = 1) then
					mkApp (coq_f_zall, [| Array.get a1b 1; mkLambda (i, t1, quoteterm (lift (-1) t4)) |])
				else
          Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected: (x:Z) (Zgt x `0`) /\\ (Zle x A)) -> B or (x: Z) (in l x) _. A [1]")
			else if (eq_constr f coq_in) && (Array.length a = 3) && (destRel (Array.get a 1) = 1) then
				mkApp (coq_f_zall_el, [| Array.get a 2; mkLambda (i, t1, quoteterm (lift (-1) t4)) |])
			else
        Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected: (x:Z) (Zgt x `0`) /\\ (Zle x A)) -> B or (x: Z) (in l x) _. A [1]")
		else
      Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected: (x:Z) (Zgt x `0`) /\\ (Zle x A)) -> B or (x: Z) (in l x) _. A [1]")
	
		in
			
		if isApp t then
		begin
			let f, a = destApplication t in
			if Array.length a = 1 then
			begin
				if eq_constr f coq_not then
					mkApp (coq_f_not, [| quoteterm (Array.get a 0) |])
				else
          Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
			end
			else if Array.length a = 2 then
			begin
				if eq_constr f coq_lt then
					mkApp (coq_f_lt, a)
				else if eq_constr f coq_le then
					mkApp (coq_f_le, a)
				else if eq_constr f coq_ge then
					mkApp (coq_f_ge, a)
				else if eq_constr f coq_gt then
					mkApp (coq_f_gt, a)
				else if eq_constr f coq_zlt then
					mkApp (coq_f_zlt, a)
				else if eq_constr f coq_zle then
					mkApp (coq_f_zle, a)
				else if eq_constr f coq_zge then
					mkApp (coq_f_zge, a)
				else if eq_constr f coq_zgt then
					mkApp (coq_f_zgt, a)
				else if eq_constr f coq_and then
					mkApp (coq_f_and, Array.map quoteterm a)
				else if eq_constr f coq_or then
					mkApp (coq_f_or, Array.map quoteterm a)
				else if (eq_constr f coq_ex) && (eq_constr (Array.get a 0) coq_nat) then
					quote_ex_nat (Array.get a 1)
				else if (eq_constr f coq_ex) && (eq_constr (Array.get a 0) coq_z) then
					quote_ex_z (Array.get a 1)
				else
          Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
			end
			else if Array.length a = 3 then
				if eq_constr f coq_eq then
					let (q, _) = interp_constr (Global.env ()) Evd.empty (extern_constr false (Global.env ()) Evd.empty (Array.get a 0)) in
						if eq_constr q coq_nat then
							mkApp (coq_f_eq, [| Array.get a 1; Array.get a 2 |])
						else if eq_constr q coq_z then
							mkApp (coq_f_zeq, [| Array.get a 1; Array.get a 2 |])
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "Only equalities in nat or Z can be QuoteTermed.")
				else if eq_constr f coq_in then
					let (q, _) = interp_constr (Global.env ()) Evd.empty (extern_constr false (Global.env ()) Evd.empty (Array.get a 0)) in
						if eq_constr q coq_nat then
							mkApp (coq_f_in, [| Array.get a 1; Array.get a 2 |])
						else if eq_constr q coq_z then
							mkApp (coq_f_zin, [| Array.get a 1; Array.get a 2 |])
						else if isApp q then
							let f', a' = destApplication q in
								if eq_constr f' coq_prod then
									let (q1, _) = interp_constr (Global.env ()) Evd.empty (extern_constr false (Global.env ()) Evd.empty (Array.get a' 0)) and
									    (q2, _) = interp_constr (Global.env ()) Evd.empty (extern_constr false (Global.env ()) Evd.empty (Array.get a' 1)) in
										if eq_constr q1 coq_nat && eq_constr q2 coq_nat then
											mkApp (coq_f_p_in, [| Array.get a 1; Array.get a 2 |])	
										else if eq_constr q1 coq_z && eq_constr q2 coq_z then
											mkApp (coq_f_p_zin, [| Array.get a 1; Array.get a 2 |])
										else
                      Errors.errorlabstrm "QuoteTerm" (Pp.str "Only In-expressions in (nat * nat) or (Z * Z) can be quoted.") 
								else
                  Errors.errorlabstrm "QuoteTerm" (Pp.str "Only In-expressions in (nat * nat) or (Z * Z) can be quoted.") 
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "Only In-expressions in (nat * nat) or (Z * Z) can be quoted.") 
				else
          Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
			else if Array.length a = 4 then
				if eq_constr f coq_succ then
					let (q, _) = interp_constr (Global.env ()) Evd.empty (extern_constr false (Global.env ()) Evd.empty (Array.get a 0)) in
						if eq_constr q coq_nat then
							mkApp (coq_f_succ, [| Array.get a 1; Array.get a 2; Array.get a 3 |])
						else if eq_constr q coq_z then
							mkApp (coq_f_zsucc, [| Array.get a 1; Array.get a 2; Array.get a 3 |])
						else
              Errors.errorlabstrm "QuoteTerm" (Pp.str "Only Succ-expressions in nat or Z can be quoted.")
				else
          Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
			else
        Errors.errorlabstrm "QuoteTerm" (Pp.str "This expression cannot be QuoteTermed.")
		end
		else
		begin
			try
				let i, t1, t2 = (destProd t) in
				try
					if (eq_constr t1 coq_nat) then
						quote_prod_nat i t1 t2
					else if (eq_constr t1 coq_z) then
						quote_prod_z i t1 t2
					else
						mkApp (coq_f_imp, [| (quoteterm t1); (quoteterm (lift (-1) t2)) |])
				with
				  Invalid_argument _ -> Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected (x:nat) A -> B")
			with
				Invalid_argument _ -> Errors.errorlabstrm "QuoteTerm" (Pp.str "Expected (x:nat) A")
		end
	end

let prterm_quoteterm a =
	let (t, _) = interp_constr (Global.env ()) Evd.empty a in
    ()
	  (*Pp.(msg_with !Pp_control.std_ft (Printer.prterm (quoteterm t) ++ fnl ()))*)

VERNAC COMMAND EXTEND QuoteTerm
| [ "QuoteTerm" constr(a) ] -> [ prterm_quoteterm a ] 
END

let quotegoal: unit Proofview.tactic =
  Goal.nf_enter (fun g ->
    let t = Goal.concl g in
	  let q = quoteterm t in
	  let newc = Tactics.make_change_arg (mkApp (my_constant "isValid", [| q |])) in
	  Tactics.change_in_concl None newc 
  )
;;

TACTIC EXTEND QuoteGoal
| [ "QuoteGoal" ] -> [ quotegoal ]
END
