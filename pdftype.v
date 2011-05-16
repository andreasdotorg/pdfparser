(** * Internals *)

Require Import SfLib.

Require Import String.
Require Import Ascii.
Require Import ZArith.
Require Import QArith.

Require Import Recdef.

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
  | PDFStream : string -> PDFObject
  | PDFNull : PDFObject
  | PDFIndirect : positive -> Zpos0 -> PDFObject -> PDFObject
  | PDFReference : positive -> Zpos0 -> PDFObject

with DictEntry : Set :=
  | DictEmpty : DictEntry
  | NextEntry : string -> PDFObject -> DictEntry -> DictEntry.


End PDF.

