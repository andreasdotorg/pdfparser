(** * Internals *)

Require Import SfLib.

Require Import List.
Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import QArith.

Require Import Recdef.

Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

(* ####################################################### *)
(** ** PDF base type *)

Module PDF.

Parameter Zpos0 : Set.

Inductive Numeric : Set :=
  | Integer : Z -> Numeric
  | Float : string -> Numeric.

Inductive PDFObject : Set :=
  | PDFBoolean : bool -> PDFObject
  | PDFNumber : Numeric -> PDFObject
  | PDFString : string -> PDFObject
  | PDFName : string -> PDFObject
  | PDFArray : list PDFObject -> PDFObject
  | PDFDictionary : DictEntry -> PDFObject
  | PDFStream : DictEntry -> string -> PDFObject
  | PDFNull : PDFObject
  | PDFIndirect : nat -> nat -> PDFObject -> PDFObject
  | PDFReference : nat -> nat -> PDFObject
(*
  | PDFIndirect : positive -> Zpos0 -> PDFObject -> PDFObject
  | PDFReference : positive -> Zpos0 -> PDFObject
*)
with DictEntry : Set :=
  | DictEmpty : DictEntry
  | NextEntry : string -> PDFObject -> DictEntry -> DictEntry.

Program Fixpoint dictFindEntry (d : DictEntry) (k : string) : option PDFObject :=
  match d with
  | DictEmpty => None
  | NextEntry k' v d' =>
    match string_dec k k' with
    | left  _ => Some v
    | right _ => dictFindEntry d' k
    end
  end.

Program Fixpoint dictFindRec (d : DictEntry) (k : string) : list PDFObject :=
  match d with
  | DictEmpty => []
  | NextEntry k' v d' =>
    let rest :=
      match v with
      | PDFDictionary dic => (dictFindRec dic k) ++ dictFindRec d' k
      | _                 => dictFindRec d' k
      end
    in
      match string_dec k k' with
      | left  _ => cons v rest
      | right _ => rest
      end
  end.

Program Fixpoint list2dict (l : list (string * PDFObject)) (d : DictEntry) : option DictEntry :=
  match l with
  | nil     => Some d
  | ((k,v)::xs) =>
    match dictFindEntry d k with
    | Some _ => None
    | None   => list2dict xs (NextEntry k v d)
    end
  end.


End PDF.

