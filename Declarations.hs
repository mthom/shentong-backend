{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Declarations where

import Control.Monad.Except
import Control.Parallel
import Environment
import Core.Primitives as Primitives
import Backend.Utils
import Core.Types
import Core.Utils
import Wrap
import Backend.Toplevel
import Backend.Core
import Backend.Sys
import Backend.Sequent
import Backend.Yacc
import Backend.Reader
import Backend.Prolog
import Backend.Track
import Backend.Load
import Backend.Writer
import Backend.Macros

{-
Copyright (c) 2015, Mark Tarver
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. The name of Mark Tarver may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}

kl_shen_initialise_arity_table :: Core.Types.KLValue ->
                                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_initialise_arity_table (!kl_V1456) = do let !appl_0 = Atom Nil
                                                !kl_if_1 <- appl_0 `pseq` (kl_V1456 `pseq` eq appl_0 kl_V1456)
                                                case kl_if_1 of
                                                    Atom (B (True)) -> do return (Atom Nil)
                                                    Atom (B (False)) -> do let pat_cond_2 kl_V1456 kl_V1456h kl_V1456t kl_V1456th kl_V1456tt = do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_DecArity) -> do kl_V1456tt `pseq` kl_shen_initialise_arity_table kl_V1456tt)))
                                                                                                                                                  !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                                                                                                                                  !appl_5 <- kl_V1456h `pseq` (kl_V1456th `pseq` (appl_4 `pseq` kl_put kl_V1456h (ApplC (wrapNamed "arity" kl_arity)) kl_V1456th appl_4))
                                                                                                                                                  appl_5 `pseq` applyWrapper appl_3 [appl_5]
                                                                               pat_cond_6 = do do kl_shen_f_error (ApplC (wrapNamed "shen.initialise_arity_table" kl_shen_initialise_arity_table))
                                                                            in case kl_V1456 of
                                                                                   !(kl_V1456@(Cons (!kl_V1456h)
                                                                                                    (!(kl_V1456t@(Cons (!kl_V1456th)
                                                                                                                       (!kl_V1456tt)))))) -> pat_cond_2 kl_V1456 kl_V1456h kl_V1456t kl_V1456th kl_V1456tt
                                                                                   _ -> pat_cond_6
                                                    _ -> throwError "if: expected boolean"

kl_arity :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_arity (!kl_V1458) = do let !appl_0 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.N (Core.Types.KI (-1))))))
                          !appl_1 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                          kl_V1458 `pseq` (appl_0 `pseq` (appl_1 `pseq` kl_getDivor kl_V1458 (ApplC (wrapNamed "arity" kl_arity)) appl_0 appl_1))

kl_systemf :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_systemf (!kl_V1460) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Shen) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_External) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Place) -> do return kl_V1460)))
                                                                                                                                                              !appl_3 <- kl_V1460 `pseq` (kl_External `pseq` kl_adjoin kl_V1460 kl_External)
                                                                                                                                                              !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                                                                                                                                              !appl_5 <- kl_Shen `pseq` (appl_3 `pseq` (appl_4 `pseq` kl_put kl_Shen (Core.Types.Atom (Core.Types.UnboundSym "shen.external-symbols")) appl_3 appl_4))
                                                                                                                                                              appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                           !appl_6 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                                                                           !appl_7 <- kl_Shen `pseq` (appl_6 `pseq` kl_get kl_Shen (Core.Types.Atom (Core.Types.UnboundSym "shen.external-symbols")) appl_6)
                                                                                           appl_7 `pseq` applyWrapper appl_1 [appl_7])))
                            !appl_8 <- intern (Core.Types.Atom (Core.Types.Str "shen"))
                            appl_8 `pseq` applyWrapper appl_0 [appl_8]

kl_adjoin :: Core.Types.KLValue ->
             Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_adjoin (!kl_V1463) (!kl_V1464) = do !kl_if_0 <- kl_V1463 `pseq` (kl_V1464 `pseq` kl_elementP kl_V1463 kl_V1464)
                                       case kl_if_0 of
                                           Atom (B (True)) -> do return kl_V1464
                                           Atom (B (False)) -> do do kl_V1463 `pseq` (kl_V1464 `pseq` klCons kl_V1463 kl_V1464)
                                           _ -> throwError "if: expected boolean"

kl_shen_lambda_form_entry :: Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_lambda_form_entry (!kl_V1466) = do let pat_cond_0 = do return (Atom Nil)
                                               pat_cond_1 = do return (Atom Nil)
                                               pat_cond_2 = do do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_ArityF) -> do let pat_cond_4 = do return (Atom Nil)
                                                                                                                                       pat_cond_5 = do do let pat_cond_6 = do return (Atom Nil)
                                                                                                                                                              pat_cond_7 = do do !appl_8 <- kl_V1466 `pseq` (kl_ArityF `pseq` kl_shen_lambda_form kl_V1466 kl_ArityF)
                                                                                                                                                                                 !appl_9 <- appl_8 `pseq` evalKL appl_8
                                                                                                                                                                                 !appl_10 <- kl_V1466 `pseq` (appl_9 `pseq` klCons kl_V1466 appl_9)
                                                                                                                                                                                 let !appl_11 = Atom Nil
                                                                                                                                                                                 appl_10 `pseq` (appl_11 `pseq` klCons appl_10 appl_11)
                                                                                                                                                           in case kl_ArityF of
                                                                                                                                                                  kl_ArityF@(Atom (N (KI 0))) -> pat_cond_6
                                                                                                                                                                  _ -> pat_cond_7
                                                                                                                                    in case kl_ArityF of
                                                                                                                                           kl_ArityF@(Atom (N (KI (-1)))) -> pat_cond_4
                                                                                                                                           _ -> pat_cond_5)))
                                                                  !appl_12 <- kl_V1466 `pseq` kl_arity kl_V1466
                                                                  appl_12 `pseq` applyWrapper appl_3 [appl_12]
                                            in case kl_V1466 of
                                                   kl_V1466@(Atom (UnboundSym "package")) -> pat_cond_0
                                                   kl_V1466@(ApplC (PL "package" _)) -> pat_cond_0
                                                   kl_V1466@(ApplC (Func "package" _)) -> pat_cond_0
                                                   kl_V1466@(Atom (UnboundSym "receive")) -> pat_cond_1
                                                   kl_V1466@(ApplC (PL "receive" _)) -> pat_cond_1
                                                   kl_V1466@(ApplC (Func "receive" _)) -> pat_cond_1
                                                   _ -> pat_cond_2

kl_shen_lambda_form :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_lambda_form (!kl_V1469) (!kl_V1470) = do let pat_cond_0 = do return kl_V1469
                                                     pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_3 <- kl_V1469 `pseq` (kl_X `pseq` kl_shen_add_end kl_V1469 kl_X)
                                                                                                                                    !appl_4 <- kl_V1470 `pseq` Primitives.subtract kl_V1470 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                    !appl_5 <- appl_3 `pseq` (appl_4 `pseq` kl_shen_lambda_form appl_3 appl_4)
                                                                                                                                    let !appl_6 = Atom Nil
                                                                                                                                    !appl_7 <- appl_5 `pseq` (appl_6 `pseq` klCons appl_5 appl_6)
                                                                                                                                    !appl_8 <- kl_X `pseq` (appl_7 `pseq` klCons kl_X appl_7)
                                                                                                                                    appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_8)))
                                                                        !appl_9 <- kl_gensym (Core.Types.Atom (Core.Types.UnboundSym "V"))
                                                                        appl_9 `pseq` applyWrapper appl_2 [appl_9]
                                                  in case kl_V1470 of
                                                         kl_V1470@(Atom (N (KI 0))) -> pat_cond_0
                                                         _ -> pat_cond_1

kl_shen_add_end :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_add_end (!kl_V1473) (!kl_V1474) = do let pat_cond_0 kl_V1473 kl_V1473h kl_V1473t = do let !appl_1 = Atom Nil
                                                                                              !appl_2 <- kl_V1474 `pseq` (appl_1 `pseq` klCons kl_V1474 appl_1)
                                                                                              kl_V1473 `pseq` (appl_2 `pseq` kl_append kl_V1473 appl_2)
                                                 pat_cond_3 = do do let !appl_4 = Atom Nil
                                                                    !appl_5 <- kl_V1474 `pseq` (appl_4 `pseq` klCons kl_V1474 appl_4)
                                                                    kl_V1473 `pseq` (appl_5 `pseq` klCons kl_V1473 appl_5)
                                              in case kl_V1473 of
                                                     !(kl_V1473@(Cons (!kl_V1473h)
                                                                      (!kl_V1473t))) -> pat_cond_0 kl_V1473 kl_V1473h kl_V1473t
                                                     _ -> pat_cond_3

kl_shen_set_lambda_form_entry :: Core.Types.KLValue ->
                                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_set_lambda_form_entry (!kl_V1476) = do let pat_cond_0 kl_V1476 kl_V1476h kl_V1476t = do !appl_1 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                                                                                kl_V1476h `pseq` (kl_V1476t `pseq` (appl_1 `pseq` kl_put kl_V1476h (ApplC (wrapNamed "shen.lambda-form" kl_shen_lambda_form)) kl_V1476t appl_1))
                                                   pat_cond_2 = do do kl_shen_f_error (ApplC (wrapNamed "shen.set-lambda-form-entry" kl_shen_set_lambda_form_entry))
                                                in case kl_V1476 of
                                                       !(kl_V1476@(Cons (!kl_V1476h)
                                                                        (!kl_V1476t))) -> pat_cond_0 kl_V1476 kl_V1476h kl_V1476t
                                                       _ -> pat_cond_2

kl_specialise :: Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_specialise (!kl_V1478) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*special*"))
                               !appl_1 <- kl_V1478 `pseq` (appl_0 `pseq` klCons kl_V1478 appl_0)
                               !appl_2 <- appl_1 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*special*")) appl_1
                               appl_2 `pseq` (kl_V1478 `pseq` kl_do appl_2 kl_V1478)

kl_unspecialise :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_unspecialise (!kl_V1480) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*special*"))
                                 !appl_1 <- kl_V1480 `pseq` (appl_0 `pseq` kl_remove kl_V1480 appl_0)
                                 !appl_2 <- appl_1 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*special*")) appl_1
                                 appl_2 `pseq` (kl_V1480 `pseq` kl_do appl_2 kl_V1480)

expr11 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr11 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*installing-kl*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_0 = Atom Nil
                appl_0 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*history*")) appl_0) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do !appl_1 <- kl_dict (Core.Types.Atom (Core.Types.N (Core.Types.KI 20000)))
                appl_1 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*")) appl_1) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*process-counter*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do !appl_2 <- kl_vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 1000)))
                appl_2 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*varcounter*")) appl_2) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do !appl_3 <- kl_vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 1000)))
                appl_3 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*prologvectors*")) appl_3) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_X) -> do return kl_X)))
                appl_4 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*demodulation-function*")) appl_4) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_5 = Atom Nil
                !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "shen.function-macro" kl_shen_function_macro)) appl_5
                !appl_7 <- appl_6 `pseq` klCons (ApplC (wrapNamed "shen.defprolog-macro" kl_shen_defprolog_macro)) appl_6
                !appl_8 <- appl_7 `pseq` klCons (ApplC (wrapNamed "shen.@s-macro" kl_shen_Ats_macro)) appl_7
                !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "shen.nl-macro" kl_shen_nl_macro)) appl_8
                !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "shen.synonyms-macro" kl_shen_synonyms_macro)) appl_9
                !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "shen.prolog-macro" kl_shen_prolog_macro)) appl_10
                !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "shen.error-macro" kl_shen_error_macro)) appl_11
                !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "shen.input-macro" kl_shen_input_macro)) appl_12
                !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "shen.output-macro" kl_shen_output_macro)) appl_13
                !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "shen.make-string-macro" kl_shen_make_string_macro)) appl_14
                !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "shen.assoc-macro" kl_shen_assoc_macro)) appl_15
                !appl_17 <- appl_16 `pseq` klCons (ApplC (wrapNamed "shen.let-macro" kl_shen_let_macro)) appl_16
                !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "shen.datatype-macro" kl_shen_datatype_macro)) appl_17
                !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.compile-macro" kl_shen_compile_macro)) appl_18
                !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "shen.put/get-macro" kl_shen_putDivget_macro)) appl_19
                !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "shen.abs-macro" kl_shen_abs_macro)) appl_20
                !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "shen.cases-macro" kl_shen_cases_macro)) appl_21
                !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "shen.timer-macro" kl_shen_timer_macro)) appl_22
                appl_23 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*macroreg*")) appl_23) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_24 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_timer_macro kl_X)))
                let !appl_25 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_cases_macro kl_X)))
                let !appl_26 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_abs_macro kl_X)))
                let !appl_27 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_putDivget_macro kl_X)))
                let !appl_28 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_compile_macro kl_X)))
                let !appl_29 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_datatype_macro kl_X)))
                let !appl_30 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_let_macro kl_X)))
                let !appl_31 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_assoc_macro kl_X)))
                let !appl_32 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_make_string_macro kl_X)))
                let !appl_33 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_output_macro kl_X)))
                let !appl_34 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_input_macro kl_X)))
                let !appl_35 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_error_macro kl_X)))
                let !appl_36 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_prolog_macro kl_X)))
                let !appl_37 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_synonyms_macro kl_X)))
                let !appl_38 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_nl_macro kl_X)))
                let !appl_39 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_Ats_macro kl_X)))
                let !appl_40 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_defprolog_macro kl_X)))
                let !appl_41 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_function_macro kl_X)))
                let !appl_42 = Atom Nil
                !appl_43 <- appl_41 `pseq` (appl_42 `pseq` klCons appl_41 appl_42)
                !appl_44 <- appl_40 `pseq` (appl_43 `pseq` klCons appl_40 appl_43)
                !appl_45 <- appl_39 `pseq` (appl_44 `pseq` klCons appl_39 appl_44)
                !appl_46 <- appl_38 `pseq` (appl_45 `pseq` klCons appl_38 appl_45)
                !appl_47 <- appl_37 `pseq` (appl_46 `pseq` klCons appl_37 appl_46)
                !appl_48 <- appl_36 `pseq` (appl_47 `pseq` klCons appl_36 appl_47)
                !appl_49 <- appl_35 `pseq` (appl_48 `pseq` klCons appl_35 appl_48)
                !appl_50 <- appl_34 `pseq` (appl_49 `pseq` klCons appl_34 appl_49)
                !appl_51 <- appl_33 `pseq` (appl_50 `pseq` klCons appl_33 appl_50)
                !appl_52 <- appl_32 `pseq` (appl_51 `pseq` klCons appl_32 appl_51)
                !appl_53 <- appl_31 `pseq` (appl_52 `pseq` klCons appl_31 appl_52)
                !appl_54 <- appl_30 `pseq` (appl_53 `pseq` klCons appl_30 appl_53)
                !appl_55 <- appl_29 `pseq` (appl_54 `pseq` klCons appl_29 appl_54)
                !appl_56 <- appl_28 `pseq` (appl_55 `pseq` klCons appl_28 appl_55)
                !appl_57 <- appl_27 `pseq` (appl_56 `pseq` klCons appl_27 appl_56)
                !appl_58 <- appl_26 `pseq` (appl_57 `pseq` klCons appl_26 appl_57)
                !appl_59 <- appl_25 `pseq` (appl_58 `pseq` klCons appl_25 appl_58)
                !appl_60 <- appl_24 `pseq` (appl_59 `pseq` klCons appl_24 appl_59)
                appl_60 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "*macros*")) appl_60) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*gensym*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_61 = Atom Nil
                appl_61 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*tracking*")) appl_61) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_62 = Atom Nil
                !appl_63 <- appl_62 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Z")) appl_62
                !appl_64 <- appl_63 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Y")) appl_63
                !appl_65 <- appl_64 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_64
                !appl_66 <- appl_65 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "W")) appl_65
                !appl_67 <- appl_66 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_66
                !appl_68 <- appl_67 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "U")) appl_67
                !appl_69 <- appl_68 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "T")) appl_68
                !appl_70 <- appl_69 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "S")) appl_69
                !appl_71 <- appl_70 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "R")) appl_70
                !appl_72 <- appl_71 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Q")) appl_71
                !appl_73 <- appl_72 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "P")) appl_72
                !appl_74 <- appl_73 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "O")) appl_73
                !appl_75 <- appl_74 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "N")) appl_74
                !appl_76 <- appl_75 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "M")) appl_75
                !appl_77 <- appl_76 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "L")) appl_76
                !appl_78 <- appl_77 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_77
                !appl_79 <- appl_78 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "J")) appl_78
                !appl_80 <- appl_79 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "I")) appl_79
                !appl_81 <- appl_80 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "H")) appl_80
                !appl_82 <- appl_81 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "G")) appl_81
                !appl_83 <- appl_82 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "F")) appl_82
                !appl_84 <- appl_83 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "E")) appl_83
                !appl_85 <- appl_84 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "D")) appl_84
                !appl_86 <- appl_85 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "C")) appl_85
                !appl_87 <- appl_86 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_86
                !appl_88 <- appl_87 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_87
                appl_88 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*alphabet*")) appl_88) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_89 = Atom Nil
                !appl_90 <- appl_89 `pseq` klCons (ApplC (wrapNamed "open" openStream)) appl_89
                !appl_91 <- appl_90 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_90
                !appl_92 <- appl_91 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "where")) appl_91
                !appl_93 <- appl_92 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_92
                !appl_94 <- appl_93 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_93
                !appl_95 <- appl_94 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_94
                !appl_96 <- appl_95 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_95
                !appl_97 <- appl_96 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_96
                !appl_98 <- appl_97 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_97
                appl_98 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*special*")) appl_98) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_99 = Atom Nil
                !appl_100 <- appl_99 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defmacro")) appl_99
                !appl_101 <- appl_100 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.read+")) appl_100
                !appl_102 <- appl_101 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defcc")) appl_101
                !appl_103 <- appl_102 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_102
                !appl_104 <- appl_103 `pseq` klCons (ApplC (wrapNamed "shen.process-datatype" kl_shen_process_datatype)) appl_103
                !appl_105 <- appl_104 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "define")) appl_104
                appl_105 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*extraspecial*")) appl_105) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*spy*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_106 = Atom Nil
                appl_106 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*datatypes*")) appl_106) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_107 = Atom Nil
                appl_107 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*alldatatypes*")) appl_107) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*shen-type-theory-enabled?*")) (Atom (B True))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_108 = Atom Nil
                appl_108 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*synonyms*")) appl_108) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_109 = Atom Nil
                appl_109 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*system*")) appl_109) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_110 = Atom Nil
                appl_110 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*signedfuncs*")) appl_110) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*maxcomplexity*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 128)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*occurs*")) (Atom (B True))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*maxinferences*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 1000000)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "*maximum-print-sequence-size*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 20)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*catch*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*infs*")) (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "*hush*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*optimise*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do klSet (Core.Types.Atom (Core.Types.UnboundSym "*version*")) (Core.Types.Atom (Core.Types.Str "Shen 20.0"))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do !appl_111 <- kl_boundP (Core.Types.Atom (Core.Types.UnboundSym "*home-directory*"))
                !kl_if_112 <- appl_111 `pseq` kl_not appl_111
                case kl_if_112 of
                    Atom (B (True)) -> do klSet (Core.Types.Atom (Core.Types.UnboundSym "*home-directory*")) (Core.Types.Atom (Core.Types.Str ""))
                    Atom (B (False)) -> do do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                    _ -> throwError "if: expected boolean") `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do !appl_113 <- kl_boundP (Core.Types.Atom (Core.Types.UnboundSym "shen.*sterror*"))
                !kl_if_114 <- appl_113 `pseq` kl_not appl_113
                case kl_if_114 of
                    Atom (B (True)) -> do !appl_115 <- value (Core.Types.Atom (Core.Types.UnboundSym "*stoutput*"))
                                          appl_115 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*sterror*")) appl_115
                    Atom (B (False)) -> do do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                    _ -> throwError "if: expected boolean") `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_116 = Atom Nil
                !appl_117 <- appl_116 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_116
                !appl_118 <- appl_117 `pseq` klCons (ApplC (wrapNamed "dict-values" kl_dict_values)) appl_117
                !appl_119 <- appl_118 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_118
                !appl_120 <- appl_119 `pseq` klCons (ApplC (wrapNamed "dict-keys" kl_dict_keys)) appl_119
                !appl_121 <- appl_120 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_120
                !appl_122 <- appl_121 `pseq` klCons (ApplC (wrapNamed "dict-fold" kl_dict_fold)) appl_121
                !appl_123 <- appl_122 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_122
                !appl_124 <- appl_123 `pseq` klCons (ApplC (wrapNamed "dict-rm" kl_dict_rm)) appl_123
                !appl_125 <- appl_124 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_124
                !appl_126 <- appl_125 `pseq` klCons (ApplC (wrapNamed "<-dict" kl_LB_dict)) appl_125
                !appl_127 <- appl_126 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_126
                !appl_128 <- appl_127 `pseq` klCons (ApplC (wrapNamed "<-dict/or" kl_LB_dictDivor)) appl_127
                !appl_129 <- appl_128 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_128
                !appl_130 <- appl_129 `pseq` klCons (ApplC (wrapNamed "dict->" kl_dict_RB)) appl_129
                !appl_131 <- appl_130 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_130
                !appl_132 <- appl_131 `pseq` klCons (ApplC (wrapNamed "dict-count" kl_dict_count)) appl_131
                !appl_133 <- appl_132 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_132
                !appl_134 <- appl_133 `pseq` klCons (ApplC (wrapNamed "dict?" kl_dictP)) appl_133
                !appl_135 <- appl_134 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_134
                !appl_136 <- appl_135 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_135
                !appl_137 <- appl_136 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_136
                !appl_138 <- appl_137 `pseq` klCons (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_137
                !appl_139 <- appl_138 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_138
                !appl_140 <- appl_139 `pseq` klCons (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_139
                !appl_141 <- appl_140 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_140
                !appl_142 <- appl_141 `pseq` klCons (ApplC (wrapNamed "include" kl_include)) appl_141
                !appl_143 <- appl_142 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_142
                !appl_144 <- appl_143 `pseq` klCons (ApplC (wrapNamed "preclude" kl_preclude)) appl_143
                !appl_145 <- appl_144 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_144
                !appl_146 <- appl_145 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_145
                !appl_147 <- appl_146 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_146
                !appl_148 <- appl_147 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_147
                !appl_149 <- appl_148 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_148
                !appl_150 <- appl_149 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_149
                !appl_151 <- appl_150 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_150
                !appl_152 <- appl_151 `pseq` klCons (ApplC (wrapNamed "<!>" kl_LBExclRB)) appl_151
                !appl_153 <- appl_152 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_152
                !appl_154 <- appl_153 `pseq` klCons (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_153
                !appl_155 <- appl_154 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_154
                !appl_156 <- appl_155 `pseq` klCons (ApplC (wrapNamed "==" kl_EqEq)) appl_155
                !appl_157 <- appl_156 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_156
                !appl_158 <- appl_157 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_157
                !appl_159 <- appl_158 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_158
                !appl_160 <- appl_159 `pseq` klCons (ApplC (wrapNamed "/" divide)) appl_159
                !appl_161 <- appl_160 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_160
                !appl_162 <- appl_161 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_161
                !appl_163 <- appl_162 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_162
                !appl_164 <- appl_163 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_163
                !appl_165 <- appl_164 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_164
                !appl_166 <- appl_165 `pseq` klCons (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_165
                !appl_167 <- appl_166 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_166
                !appl_168 <- appl_167 `pseq` klCons (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_167
                !appl_169 <- appl_168 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_168
                !appl_170 <- appl_169 `pseq` klCons (ApplC (wrapNamed "write-byte" writeByte)) appl_169
                !appl_171 <- appl_170 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_170
                !appl_172 <- appl_171 `pseq` klCons (ApplC (PL "version" kl_version)) appl_171
                !appl_173 <- appl_172 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_172
                !appl_174 <- appl_173 `pseq` klCons (ApplC (wrapNamed "variable?" kl_variableP)) appl_173
                !appl_175 <- appl_174 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_174
                !appl_176 <- appl_175 `pseq` klCons (ApplC (wrapNamed "value/or" kl_valueDivor)) appl_175
                !appl_177 <- appl_176 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_176
                !appl_178 <- appl_177 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_177
                !appl_179 <- appl_178 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_178
                !appl_180 <- appl_179 `pseq` klCons (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_179
                !appl_181 <- appl_180 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_180
                !appl_182 <- appl_181 `pseq` klCons (ApplC (wrapNamed "vector?" kl_vectorP)) appl_181
                !appl_183 <- appl_182 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_182
                !appl_184 <- appl_183 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_183
                !appl_185 <- appl_184 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_184
                !appl_186 <- appl_185 `pseq` klCons (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_185
                !appl_187 <- appl_186 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_186
                !appl_188 <- appl_187 `pseq` klCons (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_187
                !appl_189 <- appl_188 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_188
                !appl_190 <- appl_189 `pseq` klCons (ApplC (wrapNamed "untrack" kl_untrack)) appl_189
                !appl_191 <- appl_190 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_190
                !appl_192 <- appl_191 `pseq` klCons (ApplC (wrapNamed "union" kl_union)) appl_191
                !appl_193 <- appl_192 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 4))) appl_192
                !appl_194 <- appl_193 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_193
                !appl_195 <- appl_194 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 4))) appl_194
                !appl_196 <- appl_195 `pseq` klCons (ApplC (wrapNamed "unify" kl_unify)) appl_195
                !appl_197 <- appl_196 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_196
                !appl_198 <- appl_197 `pseq` klCons (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_197
                !appl_199 <- appl_198 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_198
                !appl_200 <- appl_199 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_199
                !appl_201 <- appl_200 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_200
                !appl_202 <- appl_201 `pseq` klCons (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_201
                !appl_203 <- appl_202 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_202
                !appl_204 <- appl_203 `pseq` klCons (ApplC (wrapNamed "return" kl_return)) appl_203
                !appl_205 <- appl_204 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_204
                !appl_206 <- appl_205 `pseq` klCons (ApplC (wrapNamed "type" typeA)) appl_205
                !appl_207 <- appl_206 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_206
                !appl_208 <- appl_207 `pseq` klCons (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_207
                !appl_209 <- appl_208 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_208
                !appl_210 <- appl_209 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "trap-error")) appl_209
                !appl_211 <- appl_210 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_210
                !appl_212 <- appl_211 `pseq` klCons (ApplC (wrapNamed "track" kl_track)) appl_211
                !appl_213 <- appl_212 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_212
                !appl_214 <- appl_213 `pseq` klCons (ApplC (wrapNamed "tlstr" tlstr)) appl_213
                !appl_215 <- appl_214 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_214
                !appl_216 <- appl_215 `pseq` klCons (ApplC (wrapNamed "thaw" kl_thaw)) appl_215
                !appl_217 <- appl_216 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_216
                !appl_218 <- appl_217 `pseq` klCons (ApplC (PL "tc?" kl_tcP)) appl_217
                !appl_219 <- appl_218 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_218
                !appl_220 <- appl_219 `pseq` klCons (ApplC (wrapNamed "tc" kl_tc)) appl_219
                !appl_221 <- appl_220 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_220
                !appl_222 <- appl_221 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_221
                !appl_223 <- appl_222 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_222
                !appl_224 <- appl_223 `pseq` klCons (ApplC (wrapNamed "tail" kl_tail)) appl_223
                !appl_225 <- appl_224 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_224
                !appl_226 <- appl_225 `pseq` klCons (ApplC (wrapNamed "systemf" kl_systemf)) appl_225
                !appl_227 <- appl_226 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_226
                !appl_228 <- appl_227 `pseq` klCons (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_227
                !appl_229 <- appl_228 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_228
                !appl_230 <- appl_229 `pseq` klCons (ApplC (wrapNamed "sum" kl_sum)) appl_229
                !appl_231 <- appl_230 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_230
                !appl_232 <- appl_231 `pseq` klCons (ApplC (wrapNamed "subst" kl_subst)) appl_231
                !appl_233 <- appl_232 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_232
                !appl_234 <- appl_233 `pseq` klCons (ApplC (wrapNamed "str" str)) appl_233
                !appl_235 <- appl_234 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_234
                !appl_236 <- appl_235 `pseq` klCons (ApplC (wrapNamed "string?" stringP)) appl_235
                !appl_237 <- appl_236 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_236
                !appl_238 <- appl_237 `pseq` klCons (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_237
                !appl_239 <- appl_238 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_238
                !appl_240 <- appl_239 `pseq` klCons (ApplC (wrapNamed "string->n" stringToN)) appl_239
                !appl_241 <- appl_240 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_240
                !appl_242 <- appl_241 `pseq` klCons (ApplC (PL "sterror" kl_sterror)) appl_241
                !appl_243 <- appl_242 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_242
                !appl_244 <- appl_243 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_243
                !appl_245 <- appl_244 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_244
                !appl_246 <- appl_245 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_245
                !appl_247 <- appl_246 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_246
                !appl_248 <- appl_247 `pseq` klCons (ApplC (wrapNamed "step" kl_step)) appl_247
                !appl_249 <- appl_248 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_248
                !appl_250 <- appl_249 `pseq` klCons (ApplC (wrapNamed "spy" kl_spy)) appl_249
                !appl_251 <- appl_250 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_250
                !appl_252 <- appl_251 `pseq` klCons (ApplC (wrapNamed "specialise" kl_specialise)) appl_251
                !appl_253 <- appl_252 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_252
                !appl_254 <- appl_253 `pseq` klCons (ApplC (wrapNamed "snd" kl_snd)) appl_253
                !appl_255 <- appl_254 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_254
                !appl_256 <- appl_255 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_255
                !appl_257 <- appl_256 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_256
                !appl_258 <- appl_257 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_257
                !appl_259 <- appl_258 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_258
                !appl_260 <- appl_259 `pseq` klCons (ApplC (wrapNamed "reverse" kl_reverse)) appl_259
                !appl_261 <- appl_260 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_260
                !appl_262 <- appl_261 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.require")) appl_261
                !appl_263 <- appl_262 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_262
                !appl_264 <- appl_263 `pseq` klCons (ApplC (wrapNamed "remove" kl_remove)) appl_263
                !appl_265 <- appl_264 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_264
                !appl_266 <- appl_265 `pseq` klCons (ApplC (PL "release" kl_release)) appl_265
                !appl_267 <- appl_266 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_266
                !appl_268 <- appl_267 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "receive")) appl_267
                !appl_269 <- appl_268 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_268
                !appl_270 <- appl_269 `pseq` klCons (ApplC (wrapNamed "read-char-code" kl_read_char_code)) appl_269
                !appl_271 <- appl_270 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_270
                !appl_272 <- appl_271 `pseq` klCons (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_271
                !appl_273 <- appl_272 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_272
                !appl_274 <- appl_273 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_273
                !appl_275 <- appl_274 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_274
                !appl_276 <- appl_275 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_275
                !appl_277 <- appl_276 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_276
                !appl_278 <- appl_277 `pseq` klCons (ApplC (wrapNamed "read-file-as-bytelist" kl_read_file_as_bytelist)) appl_277
                !appl_279 <- appl_278 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_278
                !appl_280 <- appl_279 `pseq` klCons (ApplC (wrapNamed "read-file-as-charlist" kl_read_file_as_charlist)) appl_279
                !appl_281 <- appl_280 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_280
                !appl_282 <- appl_281 `pseq` klCons (ApplC (wrapNamed "read-file" kl_read_file)) appl_281
                !appl_283 <- appl_282 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_282
                !appl_284 <- appl_283 `pseq` klCons (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_283
                !appl_285 <- appl_284 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_284
                !appl_286 <- appl_285 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.reassemble")) appl_285
                !appl_287 <- appl_286 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 4))) appl_286
                !appl_288 <- appl_287 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_287
                !appl_289 <- appl_288 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_288
                !appl_290 <- appl_289 `pseq` klCons (ApplC (wrapNamed "address->" addressTo)) appl_289
                !appl_291 <- appl_290 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_290
                !appl_292 <- appl_291 `pseq` klCons (ApplC (wrapNamed "protect" kl_protect)) appl_291
                !appl_293 <- appl_292 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_292
                !appl_294 <- appl_293 `pseq` klCons (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_293
                !appl_295 <- appl_294 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_294
                !appl_296 <- appl_295 `pseq` klCons (ApplC (wrapNamed "preclude" kl_preclude)) appl_295
                !appl_297 <- appl_296 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_296
                !appl_298 <- appl_297 `pseq` klCons (ApplC (wrapNamed "ps" kl_ps)) appl_297
                !appl_299 <- appl_298 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_298
                !appl_300 <- appl_299 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_299
                !appl_301 <- appl_300 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_300
                !appl_302 <- appl_301 `pseq` klCons (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_301
                !appl_303 <- appl_302 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_302
                !appl_304 <- appl_303 `pseq` klCons (ApplC (wrapNamed "profile" kl_profile)) appl_303
                !appl_305 <- appl_304 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_304
                !appl_306 <- appl_305 `pseq` klCons (ApplC (wrapNamed "print" kl_print)) appl_305
                !appl_307 <- appl_306 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_306
                !appl_308 <- appl_307 `pseq` klCons (ApplC (wrapNamed "pos" pos)) appl_307
                !appl_309 <- appl_308 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_308
                !appl_310 <- appl_309 `pseq` klCons (ApplC (PL "porters" kl_porters)) appl_309
                !appl_311 <- appl_310 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_310
                !appl_312 <- appl_311 `pseq` klCons (ApplC (PL "port" kl_port)) appl_311
                !appl_313 <- appl_312 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_312
                !appl_314 <- appl_313 `pseq` klCons (ApplC (wrapNamed "package?" kl_packageP)) appl_313
                !appl_315 <- appl_314 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_314
                !appl_316 <- appl_315 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "package")) appl_315
                !appl_317 <- appl_316 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_316
                !appl_318 <- appl_317 `pseq` klCons (ApplC (PL "os" kl_os)) appl_317
                !appl_319 <- appl_318 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_318
                !appl_320 <- appl_319 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "or")) appl_319
                !appl_321 <- appl_320 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_320
                !appl_322 <- appl_321 `pseq` klCons (ApplC (wrapNamed "optimise" kl_optimise)) appl_321
                !appl_323 <- appl_322 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_322
                !appl_324 <- appl_323 `pseq` klCons (ApplC (wrapNamed "open" openStream)) appl_323
                !appl_325 <- appl_324 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_324
                !appl_326 <- appl_325 `pseq` klCons (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_325
                !appl_327 <- appl_326 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_326
                !appl_328 <- appl_327 `pseq` klCons (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_327
                !appl_329 <- appl_328 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_328
                !appl_330 <- appl_329 `pseq` klCons (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_329
                !appl_331 <- appl_330 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_330
                !appl_332 <- appl_331 `pseq` klCons (ApplC (wrapNamed "number?" numberP)) appl_331
                !appl_333 <- appl_332 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_332
                !appl_334 <- appl_333 `pseq` klCons (ApplC (wrapNamed "n->string" nToString)) appl_333
                !appl_335 <- appl_334 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_334
                !appl_336 <- appl_335 `pseq` klCons (ApplC (wrapNamed "nth" kl_nth)) appl_335
                !appl_337 <- appl_336 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_336
                !appl_338 <- appl_337 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_337
                !appl_339 <- appl_338 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_338
                !appl_340 <- appl_339 `pseq` klCons (ApplC (wrapNamed "nl" kl_nl)) appl_339
                !appl_341 <- appl_340 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_340
                !appl_342 <- appl_341 `pseq` klCons (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_341
                !appl_343 <- appl_342 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_342
                !appl_344 <- appl_343 `pseq` klCons (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_343
                !appl_345 <- appl_344 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_344
                !appl_346 <- appl_345 `pseq` klCons (ApplC (wrapNamed "map" kl_map)) appl_345
                !appl_347 <- appl_346 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_346
                !appl_348 <- appl_347 `pseq` klCons (ApplC (wrapNamed "macroexpand" kl_macroexpand)) appl_347
                !appl_349 <- appl_348 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_348
                !appl_350 <- appl_349 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_349
                !appl_351 <- appl_350 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_350
                !appl_352 <- appl_351 `pseq` klCons (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_351
                !appl_353 <- appl_352 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_352
                !appl_354 <- appl_353 `pseq` klCons (ApplC (wrapNamed "<" lessThan)) appl_353
                !appl_355 <- appl_354 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_354
                !appl_356 <- appl_355 `pseq` klCons (ApplC (wrapNamed "load" kl_load)) appl_355
                !appl_357 <- appl_356 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_356
                !appl_358 <- appl_357 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_357
                !appl_359 <- appl_358 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_358
                !appl_360 <- appl_359 `pseq` klCons (ApplC (wrapNamed "limit" kl_limit)) appl_359
                !appl_361 <- appl_360 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_360
                !appl_362 <- appl_361 `pseq` klCons (ApplC (wrapNamed "length" kl_length)) appl_361
                !appl_363 <- appl_362 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_362
                !appl_364 <- appl_363 `pseq` klCons (ApplC (PL "language" kl_language)) appl_363
                !appl_365 <- appl_364 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_364
                !appl_366 <- appl_365 `pseq` klCons (ApplC (PL "kill" kl_kill)) appl_365
                !appl_367 <- appl_366 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_366
                !appl_368 <- appl_367 `pseq` klCons (ApplC (PL "it" kl_it)) appl_367
                !appl_369 <- appl_368 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_368
                !appl_370 <- appl_369 `pseq` klCons (ApplC (wrapNamed "internal" kl_internal)) appl_369
                !appl_371 <- appl_370 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_370
                !appl_372 <- appl_371 `pseq` klCons (ApplC (wrapNamed "intersection" kl_intersection)) appl_371
                !appl_373 <- appl_372 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_372
                !appl_374 <- appl_373 `pseq` klCons (ApplC (PL "implementation" kl_implementation)) appl_373
                !appl_375 <- appl_374 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_374
                !appl_376 <- appl_375 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_375
                !appl_377 <- appl_376 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_376
                !appl_378 <- appl_377 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_377
                !appl_379 <- appl_378 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_378
                !appl_380 <- appl_379 `pseq` klCons (ApplC (PL "inferences" kl_inferences)) appl_379
                !appl_381 <- appl_380 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 4))) appl_380
                !appl_382 <- appl_381 `pseq` klCons (ApplC (wrapNamed "identical" kl_identical)) appl_381
                !appl_383 <- appl_382 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_382
                !appl_384 <- appl_383 `pseq` klCons (ApplC (wrapNamed "intern" intern)) appl_383
                !appl_385 <- appl_384 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_384
                !appl_386 <- appl_385 `pseq` klCons (ApplC (wrapNamed "integer?" kl_integerP)) appl_385
                !appl_387 <- appl_386 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_386
                !appl_388 <- appl_387 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_387
                !appl_389 <- appl_388 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_388
                !appl_390 <- appl_389 `pseq` klCons (ApplC (wrapNamed "head" kl_head)) appl_389
                !appl_391 <- appl_390 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_390
                !appl_392 <- appl_391 `pseq` klCons (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_391
                !appl_393 <- appl_392 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_392
                !appl_394 <- appl_393 `pseq` klCons (ApplC (wrapNamed "hdv" kl_hdv)) appl_393
                !appl_395 <- appl_394 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_394
                !appl_396 <- appl_395 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_395
                !appl_397 <- appl_396 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_396
                !appl_398 <- appl_397 `pseq` klCons (ApplC (wrapNamed "hash" kl_hash)) appl_397
                !appl_399 <- appl_398 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_398
                !appl_400 <- appl_399 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_399
                !appl_401 <- appl_400 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_400
                !appl_402 <- appl_401 `pseq` klCons (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_401
                !appl_403 <- appl_402 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_402
                !appl_404 <- appl_403 `pseq` klCons (ApplC (wrapNamed ">" greaterThan)) appl_403
                !appl_405 <- appl_404 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_404
                !appl_406 <- appl_405 `pseq` klCons (ApplC (wrapNamed "<-vector/or" kl_LB_vectorDivor)) appl_405
                !appl_407 <- appl_406 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_406
                !appl_408 <- appl_407 `pseq` klCons (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_407
                !appl_409 <- appl_408 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_408
                !appl_410 <- appl_409 `pseq` klCons (ApplC (wrapNamed "<-address/or" kl_LB_addressDivor)) appl_409
                !appl_411 <- appl_410 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_410
                !appl_412 <- appl_411 `pseq` klCons (ApplC (wrapNamed "<-address" addressFrom)) appl_411
                !appl_413 <- appl_412 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_412
                !appl_414 <- appl_413 `pseq` klCons (ApplC (wrapNamed "address->" addressTo)) appl_413
                !appl_415 <- appl_414 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_414
                !appl_416 <- appl_415 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_415
                !appl_417 <- appl_416 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 4))) appl_416
                !appl_418 <- appl_417 `pseq` klCons (ApplC (wrapNamed "get/or" kl_getDivor)) appl_417
                !appl_419 <- appl_418 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_418
                !appl_420 <- appl_419 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_419
                !appl_421 <- appl_420 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_420
                !appl_422 <- appl_421 `pseq` klCons (ApplC (wrapNamed "gensym" kl_gensym)) appl_421
                !appl_423 <- appl_422 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_422
                !appl_424 <- appl_423 `pseq` klCons (ApplC (wrapNamed "fst" kl_fst)) appl_423
                !appl_425 <- appl_424 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_424
                !appl_426 <- appl_425 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "freeze")) appl_425
                !appl_427 <- appl_426 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 5))) appl_426
                !appl_428 <- appl_427 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "findall")) appl_427
                !appl_429 <- appl_428 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_428
                !appl_430 <- appl_429 `pseq` klCons (ApplC (wrapNamed "for-each" kl_for_each)) appl_429
                !appl_431 <- appl_430 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_430
                !appl_432 <- appl_431 `pseq` klCons (ApplC (wrapNamed "filter" kl_filter)) appl_431
                !appl_433 <- appl_432 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_432
                !appl_434 <- appl_433 `pseq` klCons (ApplC (wrapNamed "fold-right" kl_fold_right)) appl_433
                !appl_435 <- appl_434 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_434
                !appl_436 <- appl_435 `pseq` klCons (ApplC (wrapNamed "fold-left" kl_fold_left)) appl_435
                !appl_437 <- appl_436 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_436
                !appl_438 <- appl_437 `pseq` klCons (ApplC (wrapNamed "fix" kl_fix)) appl_437
                !appl_439 <- appl_438 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_438
                !appl_440 <- appl_439 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_439
                !appl_441 <- appl_440 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_440
                !appl_442 <- appl_441 `pseq` klCons (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_441
                !appl_443 <- appl_442 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_442
                !appl_444 <- appl_443 `pseq` klCons (ApplC (wrapNamed "external" kl_external)) appl_443
                !appl_445 <- appl_444 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_444
                !appl_446 <- appl_445 `pseq` klCons (ApplC (wrapNamed "explode" kl_explode)) appl_445
                !appl_447 <- appl_446 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_446
                !appl_448 <- appl_447 `pseq` klCons (ApplC (wrapNamed "exit" kl_exit)) appl_447
                !appl_449 <- appl_448 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_448
                !appl_450 <- appl_449 `pseq` klCons (ApplC (wrapNamed "eval-kl" evalKL)) appl_449
                !appl_451 <- appl_450 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_450
                !appl_452 <- appl_451 `pseq` klCons (ApplC (wrapNamed "eval" kl_eval)) appl_451
                !appl_453 <- appl_452 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_452
                !appl_454 <- appl_453 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.interror")) appl_453
                !appl_455 <- appl_454 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_454
                !appl_456 <- appl_455 `pseq` klCons (ApplC (wrapNamed "error-to-string" errorToString)) appl_455
                !appl_457 <- appl_456 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_456
                !appl_458 <- appl_457 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "enable-type-theory")) appl_457
                !appl_459 <- appl_458 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_458
                !appl_460 <- appl_459 `pseq` klCons (ApplC (wrapNamed "empty?" kl_emptyP)) appl_459
                !appl_461 <- appl_460 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_460
                !appl_462 <- appl_461 `pseq` klCons (ApplC (wrapNamed "element?" kl_elementP)) appl_461
                !appl_463 <- appl_462 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_462
                !appl_464 <- appl_463 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_463
                !appl_465 <- appl_464 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_464
                !appl_466 <- appl_465 `pseq` klCons (ApplC (wrapNamed "difference" kl_difference)) appl_465
                !appl_467 <- appl_466 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_466
                !appl_468 <- appl_467 `pseq` klCons (ApplC (wrapNamed "destroy" kl_destroy)) appl_467
                !appl_469 <- appl_468 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_468
                !appl_470 <- appl_469 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "declare")) appl_469
                !appl_471 <- appl_470 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_470
                !appl_472 <- appl_471 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_471
                !appl_473 <- appl_472 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_472
                !appl_474 <- appl_473 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_473
                !appl_475 <- appl_474 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_474
                !appl_476 <- appl_475 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_475
                !appl_477 <- appl_476 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_476
                !appl_478 <- appl_477 `pseq` klCons (ApplC (wrapNamed "concat" kl_concat)) appl_477
                !appl_479 <- appl_478 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_478
                !appl_480 <- appl_479 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_479
                !appl_481 <- appl_480 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_480
                !appl_482 <- appl_481 `pseq` klCons (ApplC (wrapNamed "close" closeStream)) appl_481
                !appl_483 <- appl_482 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_482
                !appl_484 <- appl_483 `pseq` klCons (ApplC (wrapNamed "cd" kl_cd)) appl_483
                !appl_485 <- appl_484 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_484
                !appl_486 <- appl_485 `pseq` klCons (ApplC (wrapNamed "bound?" kl_boundP)) appl_485
                !appl_487 <- appl_486 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_486
                !appl_488 <- appl_487 `pseq` klCons (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_487
                !appl_489 <- appl_488 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_488
                !appl_490 <- appl_489 `pseq` klCons (ApplC (wrapNamed "assoc" kl_assoc)) appl_489
                !appl_491 <- appl_490 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_490
                !appl_492 <- appl_491 `pseq` klCons (ApplC (wrapNamed "arity" kl_arity)) appl_491
                !appl_493 <- appl_492 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_492
                !appl_494 <- appl_493 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_493
                !appl_495 <- appl_494 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_494
                !appl_496 <- appl_495 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "and")) appl_495
                !appl_497 <- appl_496 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) appl_496
                !appl_498 <- appl_497 `pseq` klCons (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_497
                !appl_499 <- appl_498 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_498
                !appl_500 <- appl_499 `pseq` klCons (ApplC (wrapNamed "absvector" absvector)) appl_499
                !appl_501 <- appl_500 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_500
                !appl_502 <- appl_501 `pseq` klCons (ApplC (wrapNamed "absvector?" absvectorP)) appl_501
                !appl_503 <- appl_502 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_502
                !appl_504 <- appl_503 `pseq` klCons (ApplC (PL "abort" kl_abort)) appl_503
                appl_504 `pseq` kl_shen_initialise_arity_table appl_504) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do !appl_505 <- intern (Core.Types.Atom (Core.Types.Str "shen"))
                !appl_506 <- kl_vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                let !appl_507 = Atom Nil
                !appl_508 <- appl_507 `pseq` klCons (ApplC (wrapNamed "dict-values" kl_dict_values)) appl_507
                !appl_509 <- appl_508 `pseq` klCons (ApplC (wrapNamed "dict-keys" kl_dict_keys)) appl_508
                !appl_510 <- appl_509 `pseq` klCons (ApplC (wrapNamed "dict-fold" kl_dict_fold)) appl_509
                !appl_511 <- appl_510 `pseq` klCons (ApplC (wrapNamed "dict-rm" kl_dict_rm)) appl_510
                !appl_512 <- appl_511 `pseq` klCons (ApplC (wrapNamed "<-dict" kl_LB_dict)) appl_511
                !appl_513 <- appl_512 `pseq` klCons (ApplC (wrapNamed "<-dict/or" kl_LB_dictDivor)) appl_512
                !appl_514 <- appl_513 `pseq` klCons (ApplC (wrapNamed "dict->" kl_dict_RB)) appl_513
                !appl_515 <- appl_514 `pseq` klCons (ApplC (wrapNamed "dict-count" kl_dict_count)) appl_514
                !appl_516 <- appl_515 `pseq` klCons (ApplC (wrapNamed "dict?" kl_dictP)) appl_515
                !appl_517 <- appl_516 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_516
                !appl_518 <- appl_517 `pseq` klCons (ApplC (wrapNamed "absvector" absvector)) appl_517
                !appl_519 <- appl_518 `pseq` klCons (ApplC (wrapNamed "absvector?" absvectorP)) appl_518
                !appl_520 <- appl_519 `pseq` klCons (ApplC (wrapNamed "address->" addressTo)) appl_519
                !appl_521 <- appl_520 `pseq` klCons (ApplC (wrapNamed "<-address/or" kl_LB_addressDivor)) appl_520
                !appl_522 <- appl_521 `pseq` klCons (ApplC (wrapNamed "<-address" addressFrom)) appl_521
                !appl_523 <- appl_522 `pseq` klCons (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_522
                !appl_524 <- appl_523 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "and")) appl_523
                !appl_525 <- appl_524 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_524
                !appl_526 <- appl_525 `pseq` klCons (ApplC (PL "abort" kl_abort)) appl_525
                !appl_527 <- appl_526 `pseq` klCons (ApplC (wrapNamed "arity" kl_arity)) appl_526
                !appl_528 <- appl_527 `pseq` klCons (ApplC (wrapNamed "assoc" kl_assoc)) appl_527
                !appl_529 <- appl_528 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "bar!")) appl_528
                !appl_530 <- appl_529 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_529
                !appl_531 <- appl_530 `pseq` klCons (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_530
                !appl_532 <- appl_531 `pseq` klCons (ApplC (wrapNamed "bound?" kl_boundP)) appl_531
                !appl_533 <- appl_532 `pseq` klCons (ApplC (wrapNamed "bind" kl_bind)) appl_532
                !appl_534 <- appl_533 `pseq` klCons (ApplC (wrapNamed "close" closeStream)) appl_533
                !appl_535 <- appl_534 `pseq` klCons (ApplC (wrapNamed "call" kl_call)) appl_534
                !appl_536 <- appl_535 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "cases")) appl_535
                !appl_537 <- appl_536 `pseq` klCons (ApplC (wrapNamed "cd" kl_cd)) appl_536
                !appl_538 <- appl_537 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_537
                !appl_539 <- appl_538 `pseq` klCons (ApplC (wrapNamed "concat" kl_concat)) appl_538
                !appl_540 <- appl_539 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "cond")) appl_539
                !appl_541 <- appl_540 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_540
                !appl_542 <- appl_541 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_541
                !appl_543 <- appl_542 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_542
                !appl_544 <- appl_543 `pseq` klCons (ApplC (wrapNamed "cut" kl_cut)) appl_543
                !appl_545 <- appl_544 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "datatype")) appl_544
                !appl_546 <- appl_545 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "declare")) appl_545
                !appl_547 <- appl_546 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defprolog")) appl_546
                !appl_548 <- appl_547 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defcc")) appl_547
                !appl_549 <- appl_548 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defmacro")) appl_548
                !appl_550 <- appl_549 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "define")) appl_549
                !appl_551 <- appl_550 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defun")) appl_550
                !appl_552 <- appl_551 `pseq` klCons (ApplC (wrapNamed "destroy" kl_destroy)) appl_551
                !appl_553 <- appl_552 `pseq` klCons (ApplC (wrapNamed "difference" kl_difference)) appl_552
                !appl_554 <- appl_553 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_553
                !appl_555 <- appl_554 `pseq` klCons (ApplC (wrapNamed "element?" kl_elementP)) appl_554
                !appl_556 <- appl_555 `pseq` klCons (ApplC (wrapNamed "exit" kl_exit)) appl_555
                !appl_557 <- appl_556 `pseq` klCons (ApplC (wrapNamed "empty?" kl_emptyP)) appl_556
                !appl_558 <- appl_557 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "error")) appl_557
                !appl_559 <- appl_558 `pseq` klCons (ApplC (wrapNamed "error-to-string" errorToString)) appl_558
                !appl_560 <- appl_559 `pseq` klCons (ApplC (wrapNamed "eval" kl_eval)) appl_559
                !appl_561 <- appl_560 `pseq` klCons (ApplC (wrapNamed "eval-kl" evalKL)) appl_560
                !appl_562 <- appl_561 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "exception")) appl_561
                !appl_563 <- appl_562 `pseq` klCons (ApplC (wrapNamed "external" kl_external)) appl_562
                !appl_564 <- appl_563 `pseq` klCons (ApplC (wrapNamed "explode" kl_explode)) appl_563
                !appl_565 <- appl_564 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "enable-type-theory")) appl_564
                !appl_566 <- appl_565 `pseq` klCons (Atom (B False)) appl_565
                !appl_567 <- appl_566 `pseq` klCons (ApplC (wrapNamed "filter" kl_filter)) appl_566
                !appl_568 <- appl_567 `pseq` klCons (ApplC (wrapNamed "fold-left" kl_fold_left)) appl_567
                !appl_569 <- appl_568 `pseq` klCons (ApplC (wrapNamed "fold-right" kl_fold_right)) appl_568
                !appl_570 <- appl_569 `pseq` klCons (ApplC (wrapNamed "for-each" kl_for_each)) appl_569
                !appl_571 <- appl_570 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "findall")) appl_570
                !appl_572 <- appl_571 `pseq` klCons (ApplC (wrapNamed "fwhen" kl_fwhen)) appl_571
                !appl_573 <- appl_572 `pseq` klCons (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_572
                !appl_574 <- appl_573 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_573
                !appl_575 <- appl_574 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "file")) appl_574
                !appl_576 <- appl_575 `pseq` klCons (ApplC (wrapNamed "fix" kl_fix)) appl_575
                !appl_577 <- appl_576 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "freeze")) appl_576
                !appl_578 <- appl_577 `pseq` klCons (ApplC (wrapNamed "fst" kl_fst)) appl_577
                !appl_579 <- appl_578 `pseq` klCons (ApplC (wrapNamed "function" kl_function)) appl_578
                !appl_580 <- appl_579 `pseq` klCons (ApplC (wrapNamed "gensym" kl_gensym)) appl_579
                !appl_581 <- appl_580 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_580
                !appl_582 <- appl_581 `pseq` klCons (ApplC (wrapNamed "get/or" kl_getDivor)) appl_581
                !appl_583 <- appl_582 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_582
                !appl_584 <- appl_583 `pseq` klCons (ApplC (wrapNamed "hash" kl_hash)) appl_583
                !appl_585 <- appl_584 `pseq` klCons (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_584
                !appl_586 <- appl_585 `pseq` klCons (ApplC (wrapNamed "hdv" kl_hdv)) appl_585
                !appl_587 <- appl_586 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_586
                !appl_588 <- appl_587 `pseq` klCons (ApplC (wrapNamed "head" kl_head)) appl_587
                !appl_589 <- appl_588 `pseq` klCons (ApplC (wrapNamed "identical" kl_identical)) appl_588
                !appl_590 <- appl_589 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_589
                !appl_591 <- appl_590 `pseq` klCons (ApplC (PL "implementation" kl_implementation)) appl_590
                !appl_592 <- appl_591 `pseq` klCons (ApplC (wrapNamed "internal" kl_internal)) appl_591
                !appl_593 <- appl_592 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "in")) appl_592
                !appl_594 <- appl_593 `pseq` klCons (ApplC (PL "it" kl_it)) appl_593
                !appl_595 <- appl_594 `pseq` klCons (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_594
                !appl_596 <- appl_595 `pseq` klCons (ApplC (wrapNamed "include" kl_include)) appl_595
                !appl_597 <- appl_596 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_596
                !appl_598 <- appl_597 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_597
                !appl_599 <- appl_598 `pseq` klCons (ApplC (wrapNamed "integer?" kl_integerP)) appl_598
                !appl_600 <- appl_599 `pseq` klCons (ApplC (wrapNamed "intern" intern)) appl_599
                !appl_601 <- appl_600 `pseq` klCons (ApplC (PL "inferences" kl_inferences)) appl_600
                !appl_602 <- appl_601 `pseq` klCons (ApplC (wrapNamed "intersection" kl_intersection)) appl_601
                !appl_603 <- appl_602 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "is")) appl_602
                !appl_604 <- appl_603 `pseq` klCons (ApplC (PL "kill" kl_kill)) appl_603
                !appl_605 <- appl_604 `pseq` klCons (ApplC (PL "language" kl_language)) appl_604
                !appl_606 <- appl_605 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_605
                !appl_607 <- appl_606 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lazy")) appl_606
                !appl_608 <- appl_607 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_607
                !appl_609 <- appl_608 `pseq` klCons (ApplC (wrapNamed "length" kl_length)) appl_608
                !appl_610 <- appl_609 `pseq` klCons (ApplC (wrapNamed "limit" kl_limit)) appl_609
                !appl_611 <- appl_610 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_610
                !appl_612 <- appl_611 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_611
                !appl_613 <- appl_612 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "loaded")) appl_612
                !appl_614 <- appl_613 `pseq` klCons (ApplC (wrapNamed "load" kl_load)) appl_613
                !appl_615 <- appl_614 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "make-string")) appl_614
                !appl_616 <- appl_615 `pseq` klCons (ApplC (wrapNamed "map" kl_map)) appl_615
                !appl_617 <- appl_616 `pseq` klCons (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_616
                !appl_618 <- appl_617 `pseq` klCons (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_617
                !appl_619 <- appl_618 `pseq` klCons (ApplC (wrapNamed "macroexpand" kl_macroexpand)) appl_618
                !appl_620 <- appl_619 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "mode")) appl_619
                !appl_621 <- appl_620 `pseq` klCons (ApplC (wrapNamed "nl" kl_nl)) appl_620
                !appl_622 <- appl_621 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_621
                !appl_623 <- appl_622 `pseq` klCons (ApplC (wrapNamed "nth" kl_nth)) appl_622
                !appl_624 <- appl_623 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "null")) appl_623
                !appl_625 <- appl_624 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_624
                !appl_626 <- appl_625 `pseq` klCons (ApplC (wrapNamed "number?" numberP)) appl_625
                !appl_627 <- appl_626 `pseq` klCons (ApplC (wrapNamed "n->string" nToString)) appl_626
                !appl_628 <- appl_627 `pseq` klCons (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_627
                !appl_629 <- appl_628 `pseq` klCons (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_628
                !appl_630 <- appl_629 `pseq` klCons (ApplC (wrapNamed "open" openStream)) appl_629
                !appl_631 <- appl_630 `pseq` klCons (ApplC (wrapNamed "optimise" kl_optimise)) appl_630
                !appl_632 <- appl_631 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "or")) appl_631
                !appl_633 <- appl_632 `pseq` klCons (ApplC (PL "os" kl_os)) appl_632
                !appl_634 <- appl_633 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "out")) appl_633
                !appl_635 <- appl_634 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "output")) appl_634
                !appl_636 <- appl_635 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "package")) appl_635
                !appl_637 <- appl_636 `pseq` klCons (ApplC (PL "port" kl_port)) appl_636
                !appl_638 <- appl_637 `pseq` klCons (ApplC (PL "porters" kl_porters)) appl_637
                !appl_639 <- appl_638 `pseq` klCons (ApplC (wrapNamed "pos" pos)) appl_638
                !appl_640 <- appl_639 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_639
                !appl_641 <- appl_640 `pseq` klCons (ApplC (wrapNamed "print" kl_print)) appl_640
                !appl_642 <- appl_641 `pseq` klCons (ApplC (wrapNamed "profile" kl_profile)) appl_641
                !appl_643 <- appl_642 `pseq` klCons (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_642
                !appl_644 <- appl_643 `pseq` klCons (ApplC (wrapNamed "protect" kl_protect)) appl_643
                !appl_645 <- appl_644 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "prolog?")) appl_644
                !appl_646 <- appl_645 `pseq` klCons (ApplC (wrapNamed "ps" kl_ps)) appl_645
                !appl_647 <- appl_646 `pseq` klCons (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_646
                !appl_648 <- appl_647 `pseq` klCons (ApplC (wrapNamed "preclude" kl_preclude)) appl_647
                !appl_649 <- appl_648 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_648
                !appl_650 <- appl_649 `pseq` klCons (ApplC (wrapNamed "package?" kl_packageP)) appl_649
                !appl_651 <- appl_650 `pseq` klCons (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_650
                !appl_652 <- appl_651 `pseq` klCons (ApplC (wrapNamed "read-char-code" kl_read_char_code)) appl_651
                !appl_653 <- appl_652 `pseq` klCons (ApplC (wrapNamed "read-file-as-charlist" kl_read_file_as_charlist)) appl_652
                !appl_654 <- appl_653 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_653
                !appl_655 <- appl_654 `pseq` klCons (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_654
                !appl_656 <- appl_655 `pseq` klCons (ApplC (wrapNamed "read-file-as-bytelist" kl_read_file_as_bytelist)) appl_655
                !appl_657 <- appl_656 `pseq` klCons (ApplC (wrapNamed "read-file" kl_read_file)) appl_656
                !appl_658 <- appl_657 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "receive")) appl_657
                !appl_659 <- appl_658 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_658
                !appl_660 <- appl_659 `pseq` klCons (ApplC (PL "release" kl_release)) appl_659
                !appl_661 <- appl_660 `pseq` klCons (ApplC (wrapNamed "remove" kl_remove)) appl_660
                !appl_662 <- appl_661 `pseq` klCons (ApplC (wrapNamed "reverse" kl_reverse)) appl_661
                !appl_663 <- appl_662 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "run")) appl_662
                !appl_664 <- appl_663 `pseq` klCons (ApplC (wrapNamed "str" str)) appl_663
                !appl_665 <- appl_664 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "save")) appl_664
                !appl_666 <- appl_665 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_665
                !appl_667 <- appl_666 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_666
                !appl_668 <- appl_667 `pseq` klCons (ApplC (wrapNamed "snd" kl_snd)) appl_667
                !appl_669 <- appl_668 `pseq` klCons (ApplC (wrapNamed "specialise" kl_specialise)) appl_668
                !appl_670 <- appl_669 `pseq` klCons (ApplC (wrapNamed "spy" kl_spy)) appl_669
                !appl_671 <- appl_670 `pseq` klCons (ApplC (wrapNamed "step" kl_step)) appl_670
                !appl_672 <- appl_671 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_671
                !appl_673 <- appl_672 `pseq` klCons (ApplC (PL "sterror" kl_sterror)) appl_672
                !appl_674 <- appl_673 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_673
                !appl_675 <- appl_674 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_674
                !appl_676 <- appl_675 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_675
                !appl_677 <- appl_676 `pseq` klCons (ApplC (wrapNamed "string->n" stringToN)) appl_676
                !appl_678 <- appl_677 `pseq` klCons (ApplC (wrapNamed "string?" stringP)) appl_677
                !appl_679 <- appl_678 `pseq` klCons (ApplC (wrapNamed "subst" kl_subst)) appl_678
                !appl_680 <- appl_679 `pseq` klCons (ApplC (wrapNamed "sum" kl_sum)) appl_679
                !appl_681 <- appl_680 `pseq` klCons (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_680
                !appl_682 <- appl_681 `pseq` klCons (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_681
                !appl_683 <- appl_682 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_682
                !appl_684 <- appl_683 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "synonyms")) appl_683
                !appl_685 <- appl_684 `pseq` klCons (ApplC (wrapNamed "systemf" kl_systemf)) appl_684
                !appl_686 <- appl_685 `pseq` klCons (ApplC (wrapNamed "tail" kl_tail)) appl_685
                !appl_687 <- appl_686 `pseq` klCons (ApplC (wrapNamed "tlv" kl_tlv)) appl_686
                !appl_688 <- appl_687 `pseq` klCons (ApplC (wrapNamed "tlstr" tlstr)) appl_687
                !appl_689 <- appl_688 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_688
                !appl_690 <- appl_689 `pseq` klCons (ApplC (wrapNamed "tc" kl_tc)) appl_689
                !appl_691 <- appl_690 `pseq` klCons (ApplC (PL "tc?" kl_tcP)) appl_690
                !appl_692 <- appl_691 `pseq` klCons (ApplC (wrapNamed "thaw" kl_thaw)) appl_691
                !appl_693 <- appl_692 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "time")) appl_692
                !appl_694 <- appl_693 `pseq` klCons (ApplC (wrapNamed "track" kl_track)) appl_693
                !appl_695 <- appl_694 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "trap-error")) appl_694
                !appl_696 <- appl_695 `pseq` klCons (Atom (B True)) appl_695
                !appl_697 <- appl_696 `pseq` klCons (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_696
                !appl_698 <- appl_697 `pseq` klCons (ApplC (wrapNamed "type" typeA)) appl_697
                !appl_699 <- appl_698 `pseq` klCons (ApplC (wrapNamed "return" kl_return)) appl_698
                !appl_700 <- appl_699 `pseq` klCons (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_699
                !appl_701 <- appl_700 `pseq` klCons (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_700
                !appl_702 <- appl_701 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_701
                !appl_703 <- appl_702 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_702
                !appl_704 <- appl_703 `pseq` klCons (ApplC (wrapNamed "unify" kl_unify)) appl_703
                !appl_705 <- appl_704 `pseq` klCons (ApplC (wrapNamed "union" kl_union)) appl_704
                !appl_706 <- appl_705 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.unix")) appl_705
                !appl_707 <- appl_706 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_706
                !appl_708 <- appl_707 `pseq` klCons (ApplC (wrapNamed "untrack" kl_untrack)) appl_707
                !appl_709 <- appl_708 `pseq` klCons (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_708
                !appl_710 <- appl_709 `pseq` klCons (ApplC (wrapNamed "vector?" kl_vectorP)) appl_709
                !appl_711 <- appl_710 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_710
                !appl_712 <- appl_711 `pseq` klCons (ApplC (wrapNamed "<-vector/or" kl_LB_vectorDivor)) appl_711
                !appl_713 <- appl_712 `pseq` klCons (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_712
                !appl_714 <- appl_713 `pseq` klCons (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_713
                !appl_715 <- appl_714 `pseq` klCons (ApplC (wrapNamed "value/or" kl_valueDivor)) appl_714
                !appl_716 <- appl_715 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_715
                !appl_717 <- appl_716 `pseq` klCons (ApplC (wrapNamed "variable?" kl_variableP)) appl_716
                !appl_718 <- appl_717 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "verified")) appl_717
                !appl_719 <- appl_718 `pseq` klCons (ApplC (PL "version" kl_version)) appl_718
                !appl_720 <- appl_719 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "warn")) appl_719
                !appl_721 <- appl_720 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "when")) appl_720
                !appl_722 <- appl_721 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "where")) appl_721
                !appl_723 <- appl_722 `pseq` klCons (ApplC (wrapNamed "write-byte" writeByte)) appl_722
                !appl_724 <- appl_723 `pseq` klCons (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_723
                !appl_725 <- appl_724 `pseq` klCons (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_724
                !appl_726 <- appl_506 `pseq` (appl_725 `pseq` klCons appl_506 appl_725)
                !appl_727 <- appl_726 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ">>")) appl_726
                !appl_728 <- appl_727 `pseq` klCons (ApplC (wrapNamed "<" lessThan)) appl_727
                !appl_729 <- appl_728 `pseq` klCons (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_728
                !appl_730 <- appl_729 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_729
                !appl_731 <- appl_730 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_730
                !appl_732 <- appl_731 `pseq` klCons (ApplC (wrapNamed "/" divide)) appl_731
                !appl_733 <- appl_732 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_732
                !appl_734 <- appl_733 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "$")) appl_733
                !appl_735 <- appl_734 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "=!")) appl_734
                !appl_736 <- appl_735 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "/.")) appl_735
                !appl_737 <- appl_736 `pseq` klCons (ApplC (wrapNamed ">" greaterThan)) appl_736
                !appl_738 <- appl_737 `pseq` klCons (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_737
                !appl_739 <- appl_738 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_738
                !appl_740 <- appl_739 `pseq` klCons (ApplC (wrapNamed "==" kl_EqEq)) appl_739
                !appl_741 <- appl_740 `pseq` klCons (ApplC (wrapNamed "<!>" kl_LBExclRB)) appl_740
                !appl_742 <- appl_741 `pseq` klCons (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_741
                !appl_743 <- appl_742 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "->")) appl_742
                !appl_744 <- appl_743 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "<-")) appl_743
                !appl_745 <- appl_744 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_744
                !appl_746 <- appl_745 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_745
                !appl_747 <- appl_746 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_746
                !appl_748 <- appl_747 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*hush*")) appl_747
                !appl_749 <- appl_748 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*porters*")) appl_748
                !appl_750 <- appl_749 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*port*")) appl_749
                !appl_751 <- appl_750 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*")) appl_750
                !appl_752 <- appl_751 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*release*")) appl_751
                !appl_753 <- appl_752 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*os*")) appl_752
                !appl_754 <- appl_753 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*macros*")) appl_753
                !appl_755 <- appl_754 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*maximum-print-sequence-size*")) appl_754
                !appl_756 <- appl_755 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*version*")) appl_755
                !appl_757 <- appl_756 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*home-directory*")) appl_756
                !appl_758 <- appl_757 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*sterror*")) appl_757
                !appl_759 <- appl_758 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*stoutput*")) appl_758
                !appl_760 <- appl_759 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*stinput*")) appl_759
                !appl_761 <- appl_760 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*implementation*")) appl_760
                !appl_762 <- appl_761 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*language*")) appl_761
                !appl_763 <- appl_762 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "_")) appl_762
                !appl_764 <- appl_763 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ":=")) appl_763
                !appl_765 <- appl_764 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ":-")) appl_764
                !appl_766 <- appl_765 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ";")) appl_765
                !appl_767 <- appl_766 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ":")) appl_766
                !appl_768 <- appl_767 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "&&")) appl_767
                !appl_769 <- appl_768 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "<--")) appl_768
                !appl_770 <- appl_769 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_769
                !appl_771 <- appl_770 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "{")) appl_770
                !appl_772 <- appl_771 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "}")) appl_771
                !appl_773 <- appl_772 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "!")) appl_772
                !appl_774 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                appl_505 `pseq` (appl_773 `pseq` (appl_774 `pseq` kl_put appl_505 (Core.Types.Atom (Core.Types.UnboundSym "shen.external-symbols")) appl_773 appl_774))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_775 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do kl_Entry `pseq` kl_shen_set_lambda_form_entry kl_Entry)))
                let !appl_776 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_datatype_error kl_X)))
                !appl_777 <- appl_776 `pseq` klCons (ApplC (wrapNamed "shen.datatype-error" kl_shen_datatype_error)) appl_776
                let !appl_778 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_tuple kl_X)))
                !appl_779 <- appl_778 `pseq` klCons (ApplC (wrapNamed "shen.tuple" kl_shen_tuple)) appl_778
                let !appl_780 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_pvar kl_X)))
                !appl_781 <- appl_780 `pseq` klCons (ApplC (wrapNamed "shen.pvar" kl_shen_pvar)) appl_780
                let !appl_782 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_dictionary kl_X)))
                !appl_783 <- appl_782 `pseq` klCons (ApplC (wrapNamed "shen.dictionary" kl_shen_dictionary)) appl_782
                let !appl_784 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_lambda_form_entry kl_X)))
                !appl_785 <- intern (Core.Types.Atom (Core.Types.Str "shen"))
                !appl_786 <- appl_785 `pseq` kl_external appl_785
                !appl_787 <- appl_784 `pseq` (appl_786 `pseq` kl_mapcan appl_784 appl_786)
                !appl_788 <- appl_783 `pseq` (appl_787 `pseq` klCons appl_783 appl_787)
                !appl_789 <- appl_781 `pseq` (appl_788 `pseq` klCons appl_781 appl_788)
                !appl_790 <- appl_779 `pseq` (appl_789 `pseq` klCons appl_779 appl_789)
                !appl_791 <- appl_777 `pseq` (appl_790 `pseq` klCons appl_777 appl_790)
                appl_775 `pseq` (appl_791 `pseq` kl_for_each appl_775 appl_791)) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
