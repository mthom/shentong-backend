{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Types where

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
import Backend.Declarations

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

kl_declare :: Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_declare (!kl_V3988) (!kl_V3989) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Record) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Variancy) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Type) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_FMult) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parameters) -> do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_Clause) -> do let !appl_6 = ApplC (Func "lambda" (Context (\(!kl_AUM_instruction) -> do let !appl_7 = ApplC (Func "lambda" (Context (\(!kl_Code) -> do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_ShenDef) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do return kl_V3988)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            !appl_10 <- kl_ShenDef `pseq` kl_shen_eval_without_macros kl_ShenDef
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            appl_10 `pseq` applyWrapper appl_9 [appl_10])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          let !appl_11 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Continuation")) appl_11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_13 <- appl_12 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "ProcessN")) appl_12
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          let !appl_14 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_15 <- kl_Code `pseq` (appl_14 `pseq` klCons kl_Code appl_14)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_16 <- appl_15 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "->")) appl_15
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_17 <- appl_13 `pseq` (appl_16 `pseq` kl_append appl_13 appl_16)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_18 <- kl_Parameters `pseq` (appl_17 `pseq` kl_append kl_Parameters appl_17)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_19 <- kl_FMult `pseq` (appl_18 `pseq` klCons kl_FMult appl_18)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_20 <- appl_19 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "define")) appl_19
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          appl_20 `pseq` applyWrapper appl_8 [appl_20])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !appl_21 <- kl_AUM_instruction `pseq` kl_shen_aum_to_shen kl_AUM_instruction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           appl_21 `pseq` applyWrapper appl_7 [appl_21])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                 !appl_22 <- kl_Clause `pseq` (kl_Parameters `pseq` kl_shen_aum kl_Clause kl_Parameters)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 appl_22 `pseq` applyWrapper appl_6 [appl_22])))
                                                                                                                                                                                                                                                                                                                                                                                let !appl_23 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_23
                                                                                                                                                                                                                                                                                                                                                                                !appl_25 <- kl_FMult `pseq` (appl_24 `pseq` klCons kl_FMult appl_24)
                                                                                                                                                                                                                                                                                                                                                                                let !appl_26 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                !appl_27 <- kl_Type `pseq` (appl_26 `pseq` klCons kl_Type appl_26)
                                                                                                                                                                                                                                                                                                                                                                                !appl_28 <- appl_27 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_27
                                                                                                                                                                                                                                                                                                                                                                                !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_28
                                                                                                                                                                                                                                                                                                                                                                                let !appl_30 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                                                                                                                                                                                                                                                                                                                                                                                let !appl_32 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                !appl_33 <- appl_31 `pseq` (appl_32 `pseq` klCons appl_31 appl_32)
                                                                                                                                                                                                                                                                                                                                                                                !appl_34 <- appl_33 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ":-")) appl_33
                                                                                                                                                                                                                                                                                                                                                                                !appl_35 <- appl_25 `pseq` (appl_34 `pseq` klCons appl_25 appl_34)
                                                                                                                                                                                                                                                                                                                                                                                appl_35 `pseq` applyWrapper appl_5 [appl_35])))
                                                                                                                                                                                                                                                                                                           !appl_36 <- kl_shen_parameters (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                                                                                                                                                                           appl_36 `pseq` applyWrapper appl_4 [appl_36])))
                                                                                                                                                                                                                                           !appl_37 <- kl_V3988 `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "shen.type-signature-of-")) kl_V3988
                                                                                                                                                                                                                                           appl_37 `pseq` applyWrapper appl_3 [appl_37])))
                                                                                                                                                                            !appl_38 <- kl_V3989 `pseq` kl_shen_demodulate kl_V3989
                                                                                                                                                                            !appl_39 <- appl_38 `pseq` kl_shen_rcons_form appl_38
                                                                                                                                                                            appl_39 `pseq` applyWrapper appl_2 [appl_39])))
                                                                                                         !appl_40 <- (do kl_V3988 `pseq` (kl_V3989 `pseq` kl_shen_variancy_test kl_V3988 kl_V3989)) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip")))
                                                                                                         appl_40 `pseq` applyWrapper appl_1 [appl_40])))
                                        !appl_41 <- kl_V3988 `pseq` (kl_V3989 `pseq` klCons kl_V3988 kl_V3989)
                                        !appl_42 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*signedfuncs*"))
                                        !appl_43 <- appl_41 `pseq` (appl_42 `pseq` klCons appl_41 appl_42)
                                        !appl_44 <- appl_43 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*signedfuncs*")) appl_43
                                        appl_44 `pseq` applyWrapper appl_0 [appl_44]

kl_shen_demodulate :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_demodulate (!kl_V3991) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Demod) -> do !kl_if_1 <- kl_Demod `pseq` (kl_V3991 `pseq` eq kl_Demod kl_V3991)
                                                                                                    case kl_if_1 of
                                                                                                        Atom (B (True)) -> do return kl_V3991
                                                                                                        Atom (B (False)) -> do do kl_Demod `pseq` kl_shen_demodulate kl_Demod
                                                                                                        _ -> throwError "if: expected boolean")))
                                    !appl_2 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*demodulation-function*"))
                                    !appl_3 <- appl_2 `pseq` (kl_V3991 `pseq` kl_shen_walk appl_2 kl_V3991)
                                    appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_variancy_test :: Core.Types.KLValue ->
                         Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_variancy_test (!kl_V3994) (!kl_V3995) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_TypeF) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Check) -> do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip")))))
                                                                                                                   !appl_2 <- let pat_cond_3 = do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                                                                                                                                  pat_cond_4 = do do !kl_if_5 <- kl_TypeF `pseq` (kl_V3995 `pseq` kl_shen_variantP kl_TypeF kl_V3995)
                                                                                                                                                     case kl_if_5 of
                                                                                                                                                         Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                                                                                                                                                         Atom (B (False)) -> do do !appl_6 <- kl_V3994 `pseq` kl_shen_app kl_V3994 (Core.Types.Atom (Core.Types.Str " may create errors\n")) (Core.Types.Atom (Core.Types.UnboundSym "shen.a"))
                                                                                                                                                                                   !appl_7 <- appl_6 `pseq` cn (Core.Types.Atom (Core.Types.Str "warning: changing the type of ")) appl_6
                                                                                                                                                                                   !appl_8 <- kl_stoutput
                                                                                                                                                                                   appl_7 `pseq` (appl_8 `pseq` kl_shen_prhush appl_7 appl_8)
                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                               in case kl_TypeF of
                                                                                                                                      kl_TypeF@(Atom (UnboundSym "symbol")) -> pat_cond_3
                                                                                                                                      kl_TypeF@(ApplC (PL "symbol"
                                                                                                                                                          _)) -> pat_cond_3
                                                                                                                                      kl_TypeF@(ApplC (Func "symbol"
                                                                                                                                                            _)) -> pat_cond_3
                                                                                                                                      _ -> pat_cond_4
                                                                                                                   appl_2 `pseq` applyWrapper appl_1 [appl_2])))
                                                   let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "shen.typecheck")
                                                   !appl_10 <- kl_V3994 `pseq` applyWrapper aw_9 [kl_V3994,
                                                                                                  Core.Types.Atom (Core.Types.UnboundSym "B")]
                                                   appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_variantP :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_variantP (!kl_V4008) (!kl_V4009) = do !kl_if_0 <- kl_V4009 `pseq` (kl_V4008 `pseq` eq kl_V4009 kl_V4008)
                                              case kl_if_0 of
                                                  Atom (B (True)) -> do return (Atom (B True))
                                                  Atom (B (False)) -> do !kl_if_1 <- let pat_cond_2 kl_V4008 kl_V4008h kl_V4008t = do let pat_cond_3 kl_V4009 kl_V4009h kl_V4009t = do return (Atom (B True))
                                                                                                                                          pat_cond_4 = do do return (Atom (B False))
                                                                                                                                       in case kl_V4009 of
                                                                                                                                              !(kl_V4009@(Cons (!kl_V4009h)
                                                                                                                                                               (!kl_V4009t))) | eqCore kl_V4009h kl_V4008h -> pat_cond_3 kl_V4009 kl_V4009h kl_V4009t
                                                                                                                                              _ -> pat_cond_4
                                                                                         pat_cond_5 = do do return (Atom (B False))
                                                                                      in case kl_V4008 of
                                                                                             !(kl_V4008@(Cons (!kl_V4008h)
                                                                                                              (!kl_V4008t))) -> pat_cond_2 kl_V4008 kl_V4008h kl_V4008t
                                                                                             _ -> pat_cond_5
                                                                         case kl_if_1 of
                                                                             Atom (B (True)) -> do !appl_6 <- kl_V4008 `pseq` tl kl_V4008
                                                                                                   !appl_7 <- kl_V4009 `pseq` tl kl_V4009
                                                                                                   appl_6 `pseq` (appl_7 `pseq` kl_shen_variantP appl_6 appl_7)
                                                                             Atom (B (False)) -> do !kl_if_8 <- let pat_cond_9 kl_V4008 kl_V4008h kl_V4008t = do !kl_if_10 <- let pat_cond_11 kl_V4009 kl_V4009h kl_V4009t = do !kl_if_12 <- kl_V4008h `pseq` kl_shen_pvarP kl_V4008h
                                                                                                                                                                                                                                !kl_if_13 <- case kl_if_12 of
                                                                                                                                                                                                                                                 Atom (B (True)) -> do !kl_if_14 <- kl_V4009h `pseq` kl_variableP kl_V4009h
                                                                                                                                                                                                                                                                       case kl_if_14 of
                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                case kl_if_13 of
                                                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                                  pat_cond_15 = do do return (Atom (B False))
                                                                                                                                                                               in case kl_V4009 of
                                                                                                                                                                                      !(kl_V4009@(Cons (!kl_V4009h)
                                                                                                                                                                                                       (!kl_V4009t))) -> pat_cond_11 kl_V4009 kl_V4009h kl_V4009t
                                                                                                                                                                                      _ -> pat_cond_15
                                                                                                                                                                 case kl_if_10 of
                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                    pat_cond_16 = do do return (Atom (B False))
                                                                                                                 in case kl_V4008 of
                                                                                                                        !(kl_V4008@(Cons (!kl_V4008h)
                                                                                                                                         (!kl_V4008t))) -> pat_cond_9 kl_V4008 kl_V4008h kl_V4008t
                                                                                                                        _ -> pat_cond_16
                                                                                                    case kl_if_8 of
                                                                                                        Atom (B (True)) -> do !appl_17 <- kl_V4008 `pseq` hd kl_V4008
                                                                                                                              !appl_18 <- kl_V4008 `pseq` tl kl_V4008
                                                                                                                              !appl_19 <- appl_17 `pseq` (appl_18 `pseq` kl_subst (Core.Types.Atom (Core.Types.UnboundSym "shen.a")) appl_17 appl_18)
                                                                                                                              !appl_20 <- kl_V4009 `pseq` hd kl_V4009
                                                                                                                              !appl_21 <- kl_V4009 `pseq` tl kl_V4009
                                                                                                                              !appl_22 <- appl_20 `pseq` (appl_21 `pseq` kl_subst (Core.Types.Atom (Core.Types.UnboundSym "shen.a")) appl_20 appl_21)
                                                                                                                              appl_19 `pseq` (appl_22 `pseq` kl_shen_variantP appl_19 appl_22)
                                                                                                        Atom (B (False)) -> do !kl_if_23 <- let pat_cond_24 kl_V4008 kl_V4008h kl_V4008t = do !kl_if_25 <- let pat_cond_26 kl_V4008h kl_V4008hh kl_V4008ht = do let pat_cond_27 kl_V4009 kl_V4009h kl_V4009hh kl_V4009ht kl_V4009t = do return (Atom (B True))
                                                                                                                                                                                                                                                                    pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                 in case kl_V4009 of
                                                                                                                                                                                                                                                                        !(kl_V4009@(Cons (!(kl_V4009h@(Cons (!kl_V4009hh)
                                                                                                                                                                                                                                                                                                            (!kl_V4009ht))))
                                                                                                                                                                                                                                                                                         (!kl_V4009t))) -> pat_cond_27 kl_V4009 kl_V4009h kl_V4009hh kl_V4009ht kl_V4009t
                                                                                                                                                                                                                                                                        _ -> pat_cond_28
                                                                                                                                                                                                               pat_cond_29 = do do return (Atom (B False))
                                                                                                                                                                                                            in case kl_V4008h of
                                                                                                                                                                                                                   !(kl_V4008h@(Cons (!kl_V4008hh)
                                                                                                                                                                                                                                     (!kl_V4008ht))) -> pat_cond_26 kl_V4008h kl_V4008hh kl_V4008ht
                                                                                                                                                                                                                   _ -> pat_cond_29
                                                                                                                                                                                              case kl_if_25 of
                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                pat_cond_30 = do do return (Atom (B False))
                                                                                                                                             in case kl_V4008 of
                                                                                                                                                    !(kl_V4008@(Cons (!kl_V4008h)
                                                                                                                                                                     (!kl_V4008t))) -> pat_cond_24 kl_V4008 kl_V4008h kl_V4008t
                                                                                                                                                    _ -> pat_cond_30
                                                                                                                               case kl_if_23 of
                                                                                                                                   Atom (B (True)) -> do !appl_31 <- kl_V4008 `pseq` hd kl_V4008
                                                                                                                                                         !appl_32 <- kl_V4008 `pseq` tl kl_V4008
                                                                                                                                                         !appl_33 <- appl_31 `pseq` (appl_32 `pseq` kl_append appl_31 appl_32)
                                                                                                                                                         !appl_34 <- kl_V4009 `pseq` hd kl_V4009
                                                                                                                                                         !appl_35 <- kl_V4009 `pseq` tl kl_V4009
                                                                                                                                                         !appl_36 <- appl_34 `pseq` (appl_35 `pseq` kl_append appl_34 appl_35)
                                                                                                                                                         appl_33 `pseq` (appl_36 `pseq` kl_shen_variantP appl_33 appl_36)
                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                        _ -> throwError "if: expected boolean"
                                                                             _ -> throwError "if: expected boolean"
                                                  _ -> throwError "if: expected boolean"

expr12 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr12 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_0 = Atom Nil
                !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_0
                !appl_2 <- appl_1 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1
                !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_2
                appl_3 `pseq` kl_declare (ApplC (wrapNamed "absvector?" absvectorP)) appl_3) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_4 = Atom Nil
                !appl_5 <- appl_4 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_4
                !appl_6 <- appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_5
                let !appl_7 = Atom Nil
                !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_7
                !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_8
                let !appl_10 = Atom Nil
                !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_11
                !appl_13 <- appl_6 `pseq` (appl_12 `pseq` klCons appl_6 appl_12)
                let !appl_14 = Atom Nil
                !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                !appl_16 <- appl_15 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_15
                !appl_17 <- appl_16 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_16
                appl_17 `pseq` kl_declare (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_17) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_18 = Atom Nil
                !appl_19 <- appl_18 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_18
                !appl_20 <- appl_19 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_19
                !appl_21 <- appl_20 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_20
                let !appl_22 = Atom Nil
                !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_23
                !appl_25 <- appl_24 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_24
                appl_25 `pseq` kl_declare (Core.Types.Atom (Core.Types.UnboundSym "and")) appl_25) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_26 = Atom Nil
                !appl_27 <- appl_26 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_26
                !appl_28 <- appl_27 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_27
                !appl_29 <- appl_28 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_28
                let !appl_30 = Atom Nil
                !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                !appl_32 <- appl_31 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_31
                !appl_33 <- appl_32 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_32
                let !appl_34 = Atom Nil
                !appl_35 <- appl_33 `pseq` (appl_34 `pseq` klCons appl_33 appl_34)
                !appl_36 <- appl_35 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_35
                !appl_37 <- appl_36 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_36
                appl_37 `pseq` kl_declare (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_37) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_38 = Atom Nil
                !appl_39 <- appl_38 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_38
                !appl_40 <- appl_39 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_39
                let !appl_41 = Atom Nil
                !appl_42 <- appl_41 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_41
                !appl_43 <- appl_42 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_42
                let !appl_44 = Atom Nil
                !appl_45 <- appl_44 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_44
                !appl_46 <- appl_45 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_45
                let !appl_47 = Atom Nil
                !appl_48 <- appl_46 `pseq` (appl_47 `pseq` klCons appl_46 appl_47)
                !appl_49 <- appl_48 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_48
                !appl_50 <- appl_43 `pseq` (appl_49 `pseq` klCons appl_43 appl_49)
                let !appl_51 = Atom Nil
                !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                !appl_53 <- appl_52 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_52
                !appl_54 <- appl_40 `pseq` (appl_53 `pseq` klCons appl_40 appl_53)
                appl_54 `pseq` kl_declare (ApplC (wrapNamed "append" kl_append)) appl_54) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_55 = Atom Nil
                !appl_56 <- appl_55 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_55
                !appl_57 <- appl_56 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_56
                !appl_58 <- appl_57 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_57
                appl_58 `pseq` kl_declare (ApplC (wrapNamed "arity" kl_arity)) appl_58) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_59 = Atom Nil
                !appl_60 <- appl_59 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_59
                !appl_61 <- appl_60 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_60
                let !appl_62 = Atom Nil
                !appl_63 <- appl_61 `pseq` (appl_62 `pseq` klCons appl_61 appl_62)
                !appl_64 <- appl_63 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_63
                let !appl_65 = Atom Nil
                !appl_66 <- appl_65 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_65
                !appl_67 <- appl_66 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_66
                let !appl_68 = Atom Nil
                !appl_69 <- appl_67 `pseq` (appl_68 `pseq` klCons appl_67 appl_68)
                !appl_70 <- appl_69 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_69
                !appl_71 <- appl_64 `pseq` (appl_70 `pseq` klCons appl_64 appl_70)
                let !appl_72 = Atom Nil
                !appl_73 <- appl_71 `pseq` (appl_72 `pseq` klCons appl_71 appl_72)
                !appl_74 <- appl_73 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_73
                !appl_75 <- appl_74 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_74
                appl_75 `pseq` kl_declare (ApplC (wrapNamed "assoc" kl_assoc)) appl_75) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_76 = Atom Nil
                !appl_77 <- appl_76 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_76
                !appl_78 <- appl_77 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_77
                !appl_79 <- appl_78 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_78
                appl_79 `pseq` kl_declare (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_79) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_80 = Atom Nil
                !appl_81 <- appl_80 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_80
                !appl_82 <- appl_81 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_81
                !appl_83 <- appl_82 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_82
                appl_83 `pseq` kl_declare (ApplC (wrapNamed "bound?" kl_boundP)) appl_83) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_84 = Atom Nil
                !appl_85 <- appl_84 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_84
                !appl_86 <- appl_85 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_85
                !appl_87 <- appl_86 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_86
                appl_87 `pseq` kl_declare (ApplC (wrapNamed "cd" kl_cd)) appl_87) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_88 = Atom Nil
                !appl_89 <- appl_88 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_88
                !appl_90 <- appl_89 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_89
                let !appl_91 = Atom Nil
                !appl_92 <- appl_91 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_91
                !appl_93 <- appl_92 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_92
                let !appl_94 = Atom Nil
                !appl_95 <- appl_93 `pseq` (appl_94 `pseq` klCons appl_93 appl_94)
                !appl_96 <- appl_95 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_95
                !appl_97 <- appl_90 `pseq` (appl_96 `pseq` klCons appl_90 appl_96)
                appl_97 `pseq` kl_declare (ApplC (wrapNamed "close" closeStream)) appl_97) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_98 = Atom Nil
                !appl_99 <- appl_98 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_98
                !appl_100 <- appl_99 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_99
                !appl_101 <- appl_100 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_100
                let !appl_102 = Atom Nil
                !appl_103 <- appl_101 `pseq` (appl_102 `pseq` klCons appl_101 appl_102)
                !appl_104 <- appl_103 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_103
                !appl_105 <- appl_104 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_104
                appl_105 `pseq` kl_declare (ApplC (wrapNamed "cn" cn)) appl_105) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_106 = Atom Nil
                !appl_107 <- appl_106 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_106
                !appl_108 <- appl_107 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.==>")) appl_107
                !appl_109 <- appl_108 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_108
                let !appl_110 = Atom Nil
                !appl_111 <- appl_110 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_110
                !appl_112 <- appl_111 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_111
                !appl_113 <- appl_112 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_112
                let !appl_114 = Atom Nil
                !appl_115 <- appl_114 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_114
                !appl_116 <- appl_115 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_115
                !appl_117 <- appl_113 `pseq` (appl_116 `pseq` klCons appl_113 appl_116)
                let !appl_118 = Atom Nil
                !appl_119 <- appl_117 `pseq` (appl_118 `pseq` klCons appl_117 appl_118)
                !appl_120 <- appl_119 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_119
                !appl_121 <- appl_120 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_120
                let !appl_122 = Atom Nil
                !appl_123 <- appl_121 `pseq` (appl_122 `pseq` klCons appl_121 appl_122)
                !appl_124 <- appl_123 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_123
                !appl_125 <- appl_109 `pseq` (appl_124 `pseq` klCons appl_109 appl_124)
                appl_125 `pseq` kl_declare (ApplC (wrapNamed "compile" kl_compile)) appl_125) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_126 = Atom Nil
                !appl_127 <- appl_126 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_126
                !appl_128 <- appl_127 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_127
                !appl_129 <- appl_128 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_128
                appl_129 `pseq` kl_declare (ApplC (wrapNamed "cons?" consP)) appl_129) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_130 = Atom Nil
                !appl_131 <- appl_130 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_130
                !appl_132 <- appl_131 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_131
                !appl_133 <- appl_132 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_132
                let !appl_134 = Atom Nil
                !appl_135 <- appl_134 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_134
                !appl_136 <- appl_135 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_135
                !appl_137 <- appl_133 `pseq` (appl_136 `pseq` klCons appl_133 appl_136)
                appl_137 `pseq` kl_declare (ApplC (wrapNamed "destroy" kl_destroy)) appl_137) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_138 = Atom Nil
                !appl_139 <- appl_138 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_138
                !appl_140 <- appl_139 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_139
                let !appl_141 = Atom Nil
                !appl_142 <- appl_141 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_141
                !appl_143 <- appl_142 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_142
                let !appl_144 = Atom Nil
                !appl_145 <- appl_144 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_144
                !appl_146 <- appl_145 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_145
                let !appl_147 = Atom Nil
                !appl_148 <- appl_146 `pseq` (appl_147 `pseq` klCons appl_146 appl_147)
                !appl_149 <- appl_148 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_148
                !appl_150 <- appl_143 `pseq` (appl_149 `pseq` klCons appl_143 appl_149)
                let !appl_151 = Atom Nil
                !appl_152 <- appl_150 `pseq` (appl_151 `pseq` klCons appl_150 appl_151)
                !appl_153 <- appl_152 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_152
                !appl_154 <- appl_140 `pseq` (appl_153 `pseq` klCons appl_140 appl_153)
                appl_154 `pseq` kl_declare (ApplC (wrapNamed "difference" kl_difference)) appl_154) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_155 = Atom Nil
                !appl_156 <- appl_155 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_155
                !appl_157 <- appl_156 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_156
                !appl_158 <- appl_157 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_157
                let !appl_159 = Atom Nil
                !appl_160 <- appl_158 `pseq` (appl_159 `pseq` klCons appl_158 appl_159)
                !appl_161 <- appl_160 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_160
                !appl_162 <- appl_161 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_161
                appl_162 `pseq` kl_declare (ApplC (wrapNamed "do" kl_do)) appl_162) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_163 = Atom Nil
                !appl_164 <- appl_163 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_163
                !appl_165 <- appl_164 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_164
                let !appl_166 = Atom Nil
                !appl_167 <- appl_166 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_166
                !appl_168 <- appl_167 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_167
                let !appl_169 = Atom Nil
                !appl_170 <- appl_168 `pseq` (appl_169 `pseq` klCons appl_168 appl_169)
                !appl_171 <- appl_170 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.==>")) appl_170
                !appl_172 <- appl_165 `pseq` (appl_171 `pseq` klCons appl_165 appl_171)
                appl_172 `pseq` kl_declare (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_172) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_173 = Atom Nil
                !appl_174 <- appl_173 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_173
                !appl_175 <- appl_174 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_174
                let !appl_176 = Atom Nil
                !appl_177 <- appl_176 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_176
                !appl_178 <- appl_177 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_177
                let !appl_179 = Atom Nil
                !appl_180 <- appl_178 `pseq` (appl_179 `pseq` klCons appl_178 appl_179)
                !appl_181 <- appl_180 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.==>")) appl_180
                !appl_182 <- appl_175 `pseq` (appl_181 `pseq` klCons appl_175 appl_181)
                appl_182 `pseq` kl_declare (ApplC (wrapNamed "<!>" kl_LBExclRB)) appl_182) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_183 = Atom Nil
                !appl_184 <- appl_183 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_183
                !appl_185 <- appl_184 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_184
                let !appl_186 = Atom Nil
                !appl_187 <- appl_186 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_186
                !appl_188 <- appl_187 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_187
                !appl_189 <- appl_185 `pseq` (appl_188 `pseq` klCons appl_185 appl_188)
                let !appl_190 = Atom Nil
                !appl_191 <- appl_189 `pseq` (appl_190 `pseq` klCons appl_189 appl_190)
                !appl_192 <- appl_191 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_191
                !appl_193 <- appl_192 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_192
                appl_193 `pseq` kl_declare (ApplC (wrapNamed "element?" kl_elementP)) appl_193) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_194 = Atom Nil
                !appl_195 <- appl_194 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_194
                !appl_196 <- appl_195 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_195
                !appl_197 <- appl_196 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_196
                appl_197 `pseq` kl_declare (ApplC (wrapNamed "empty?" kl_emptyP)) appl_197) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_198 = Atom Nil
                !appl_199 <- appl_198 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_198
                !appl_200 <- appl_199 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_199
                !appl_201 <- appl_200 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_200
                appl_201 `pseq` kl_declare (Core.Types.Atom (Core.Types.UnboundSym "enable-type-theory")) appl_201) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_202 = Atom Nil
                !appl_203 <- appl_202 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_202
                !appl_204 <- appl_203 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_203
                let !appl_205 = Atom Nil
                !appl_206 <- appl_204 `pseq` (appl_205 `pseq` klCons appl_204 appl_205)
                !appl_207 <- appl_206 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_206
                !appl_208 <- appl_207 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_207
                appl_208 `pseq` kl_declare (ApplC (wrapNamed "external" kl_external)) appl_208) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_209 = Atom Nil
                !appl_210 <- appl_209 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_209
                !appl_211 <- appl_210 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_210
                !appl_212 <- appl_211 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "exception")) appl_211
                appl_212 `pseq` kl_declare (ApplC (wrapNamed "error-to-string" errorToString)) appl_212) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_213 = Atom Nil
                !appl_214 <- appl_213 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_213
                !appl_215 <- appl_214 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_214
                let !appl_216 = Atom Nil
                !appl_217 <- appl_215 `pseq` (appl_216 `pseq` klCons appl_215 appl_216)
                !appl_218 <- appl_217 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_217
                !appl_219 <- appl_218 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_218
                appl_219 `pseq` kl_declare (ApplC (wrapNamed "explode" kl_explode)) appl_219) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_220 = Atom Nil
                !appl_221 <- appl_220 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_220
                !appl_222 <- appl_221 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_221
                appl_222 `pseq` kl_declare (ApplC (PL "fail" kl_fail)) appl_222) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_223 = Atom Nil
                !appl_224 <- appl_223 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_223
                !appl_225 <- appl_224 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_224
                !appl_226 <- appl_225 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_225
                let !appl_227 = Atom Nil
                !appl_228 <- appl_227 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_227
                !appl_229 <- appl_228 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_228
                !appl_230 <- appl_229 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_229
                let !appl_231 = Atom Nil
                !appl_232 <- appl_230 `pseq` (appl_231 `pseq` klCons appl_230 appl_231)
                !appl_233 <- appl_232 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_232
                !appl_234 <- appl_226 `pseq` (appl_233 `pseq` klCons appl_226 appl_233)
                appl_234 `pseq` kl_declare (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_234) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_235 = Atom Nil
                !appl_236 <- appl_235 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_235
                !appl_237 <- appl_236 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_236
                !appl_238 <- appl_237 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_237
                let !appl_239 = Atom Nil
                !appl_240 <- appl_239 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_239
                !appl_241 <- appl_240 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_240
                !appl_242 <- appl_241 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_241
                let !appl_243 = Atom Nil
                !appl_244 <- appl_242 `pseq` (appl_243 `pseq` klCons appl_242 appl_243)
                !appl_245 <- appl_244 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_244
                !appl_246 <- appl_238 `pseq` (appl_245 `pseq` klCons appl_238 appl_245)
                appl_246 `pseq` kl_declare (ApplC (wrapNamed "fix" kl_fix)) appl_246) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_247 = Atom Nil
                !appl_248 <- appl_247 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_247
                !appl_249 <- appl_248 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lazy")) appl_248
                let !appl_250 = Atom Nil
                !appl_251 <- appl_249 `pseq` (appl_250 `pseq` klCons appl_249 appl_250)
                !appl_252 <- appl_251 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_251
                !appl_253 <- appl_252 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_252
                appl_253 `pseq` kl_declare (Core.Types.Atom (Core.Types.UnboundSym "freeze")) appl_253) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_254 = Atom Nil
                !appl_255 <- appl_254 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_254
                !appl_256 <- appl_255 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_255
                !appl_257 <- appl_256 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_256
                let !appl_258 = Atom Nil
                !appl_259 <- appl_258 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_258
                !appl_260 <- appl_259 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_259
                !appl_261 <- appl_257 `pseq` (appl_260 `pseq` klCons appl_257 appl_260)
                appl_261 `pseq` kl_declare (ApplC (wrapNamed "fst" kl_fst)) appl_261) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_262 = Atom Nil
                !appl_263 <- appl_262 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_262
                !appl_264 <- appl_263 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_263
                !appl_265 <- appl_264 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_264
                let !appl_266 = Atom Nil
                !appl_267 <- appl_266 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_266
                !appl_268 <- appl_267 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_267
                !appl_269 <- appl_268 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_268
                let !appl_270 = Atom Nil
                !appl_271 <- appl_269 `pseq` (appl_270 `pseq` klCons appl_269 appl_270)
                !appl_272 <- appl_271 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_271
                !appl_273 <- appl_265 `pseq` (appl_272 `pseq` klCons appl_265 appl_272)
                appl_273 `pseq` kl_declare (ApplC (wrapNamed "function" kl_function)) appl_273) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_274 = Atom Nil
                !appl_275 <- appl_274 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_274
                !appl_276 <- appl_275 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_275
                !appl_277 <- appl_276 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_276
                appl_277 `pseq` kl_declare (ApplC (wrapNamed "gensym" kl_gensym)) appl_277) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_278 = Atom Nil
                !appl_279 <- appl_278 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_278
                !appl_280 <- appl_279 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_279
                let !appl_281 = Atom Nil
                !appl_282 <- appl_281 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_281
                !appl_283 <- appl_282 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_282
                !appl_284 <- appl_283 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_283
                let !appl_285 = Atom Nil
                !appl_286 <- appl_284 `pseq` (appl_285 `pseq` klCons appl_284 appl_285)
                !appl_287 <- appl_286 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_286
                !appl_288 <- appl_280 `pseq` (appl_287 `pseq` klCons appl_280 appl_287)
                appl_288 `pseq` kl_declare (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_288) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_289 = Atom Nil
                !appl_290 <- appl_289 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_289
                !appl_291 <- appl_290 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_290
                let !appl_292 = Atom Nil
                !appl_293 <- appl_292 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_292
                !appl_294 <- appl_293 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lazy")) appl_293
                let !appl_295 = Atom Nil
                !appl_296 <- appl_295 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_295
                !appl_297 <- appl_296 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_296
                !appl_298 <- appl_294 `pseq` (appl_297 `pseq` klCons appl_294 appl_297)
                let !appl_299 = Atom Nil
                !appl_300 <- appl_298 `pseq` (appl_299 `pseq` klCons appl_298 appl_299)
                !appl_301 <- appl_300 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_300
                !appl_302 <- appl_301 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_301
                let !appl_303 = Atom Nil
                !appl_304 <- appl_302 `pseq` (appl_303 `pseq` klCons appl_302 appl_303)
                !appl_305 <- appl_304 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_304
                !appl_306 <- appl_291 `pseq` (appl_305 `pseq` klCons appl_291 appl_305)
                appl_306 `pseq` kl_declare (ApplC (wrapNamed "<-vector/or" kl_LB_vectorDivor)) appl_306) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_307 = Atom Nil
                !appl_308 <- appl_307 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_307
                !appl_309 <- appl_308 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_308
                let !appl_310 = Atom Nil
                !appl_311 <- appl_310 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_310
                !appl_312 <- appl_311 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_311
                let !appl_313 = Atom Nil
                !appl_314 <- appl_312 `pseq` (appl_313 `pseq` klCons appl_312 appl_313)
                !appl_315 <- appl_314 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_314
                !appl_316 <- appl_315 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_315
                let !appl_317 = Atom Nil
                !appl_318 <- appl_316 `pseq` (appl_317 `pseq` klCons appl_316 appl_317)
                !appl_319 <- appl_318 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_318
                !appl_320 <- appl_319 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_319
                let !appl_321 = Atom Nil
                !appl_322 <- appl_320 `pseq` (appl_321 `pseq` klCons appl_320 appl_321)
                !appl_323 <- appl_322 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_322
                !appl_324 <- appl_309 `pseq` (appl_323 `pseq` klCons appl_309 appl_323)
                appl_324 `pseq` kl_declare (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_324) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_325 = Atom Nil
                !appl_326 <- appl_325 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_325
                !appl_327 <- appl_326 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_326
                let !appl_328 = Atom Nil
                !appl_329 <- appl_327 `pseq` (appl_328 `pseq` klCons appl_327 appl_328)
                !appl_330 <- appl_329 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_329
                !appl_331 <- appl_330 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_330
                appl_331 `pseq` kl_declare (ApplC (wrapNamed "vector" kl_vector)) appl_331) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_332 = Atom Nil
                !appl_333 <- appl_332 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_332
                !appl_334 <- appl_333 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_333
                !appl_335 <- appl_334 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_334
                let !appl_336 = Atom Nil
                !appl_337 <- appl_335 `pseq` (appl_336 `pseq` klCons appl_335 appl_336)
                !appl_338 <- appl_337 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_337
                !appl_339 <- appl_338 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_338
                appl_339 `pseq` kl_declare (ApplC (wrapNamed "dict" kl_dict)) appl_339) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_340 = Atom Nil
                !appl_341 <- appl_340 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_340
                !appl_342 <- appl_341 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_341
                !appl_343 <- appl_342 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_342
                appl_343 `pseq` kl_declare (ApplC (wrapNamed "dict?" kl_dictP)) appl_343) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_344 = Atom Nil
                !appl_345 <- appl_344 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_344
                !appl_346 <- appl_345 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_345
                !appl_347 <- appl_346 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_346
                let !appl_348 = Atom Nil
                !appl_349 <- appl_348 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_348
                !appl_350 <- appl_349 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_349
                !appl_351 <- appl_347 `pseq` (appl_350 `pseq` klCons appl_347 appl_350)
                appl_351 `pseq` kl_declare (ApplC (wrapNamed "dict-count" kl_dict_count)) appl_351) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_352 = Atom Nil
                !appl_353 <- appl_352 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_352
                !appl_354 <- appl_353 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_353
                !appl_355 <- appl_354 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_354
                let !appl_356 = Atom Nil
                !appl_357 <- appl_356 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_356
                !appl_358 <- appl_357 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_357
                !appl_359 <- appl_358 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_358
                let !appl_360 = Atom Nil
                !appl_361 <- appl_359 `pseq` (appl_360 `pseq` klCons appl_359 appl_360)
                !appl_362 <- appl_361 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_361
                !appl_363 <- appl_355 `pseq` (appl_362 `pseq` klCons appl_355 appl_362)
                appl_363 `pseq` kl_declare (ApplC (wrapNamed "<-dict" kl_LB_dict)) appl_363) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_364 = Atom Nil
                !appl_365 <- appl_364 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_364
                !appl_366 <- appl_365 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_365
                !appl_367 <- appl_366 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_366
                let !appl_368 = Atom Nil
                !appl_369 <- appl_368 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_368
                !appl_370 <- appl_369 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lazy")) appl_369
                let !appl_371 = Atom Nil
                !appl_372 <- appl_371 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_371
                !appl_373 <- appl_372 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_372
                !appl_374 <- appl_370 `pseq` (appl_373 `pseq` klCons appl_370 appl_373)
                let !appl_375 = Atom Nil
                !appl_376 <- appl_374 `pseq` (appl_375 `pseq` klCons appl_374 appl_375)
                !appl_377 <- appl_376 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_376
                !appl_378 <- appl_377 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_377
                let !appl_379 = Atom Nil
                !appl_380 <- appl_378 `pseq` (appl_379 `pseq` klCons appl_378 appl_379)
                !appl_381 <- appl_380 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_380
                !appl_382 <- appl_367 `pseq` (appl_381 `pseq` klCons appl_367 appl_381)
                appl_382 `pseq` kl_declare (ApplC (wrapNamed "<-dict/or" kl_LB_dictDivor)) appl_382) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_383 = Atom Nil
                !appl_384 <- appl_383 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_383
                !appl_385 <- appl_384 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_384
                !appl_386 <- appl_385 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_385
                let !appl_387 = Atom Nil
                !appl_388 <- appl_387 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_387
                !appl_389 <- appl_388 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_388
                !appl_390 <- appl_389 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_389
                let !appl_391 = Atom Nil
                !appl_392 <- appl_390 `pseq` (appl_391 `pseq` klCons appl_390 appl_391)
                !appl_393 <- appl_392 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_392
                !appl_394 <- appl_393 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_393
                let !appl_395 = Atom Nil
                !appl_396 <- appl_394 `pseq` (appl_395 `pseq` klCons appl_394 appl_395)
                !appl_397 <- appl_396 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_396
                !appl_398 <- appl_386 `pseq` (appl_397 `pseq` klCons appl_386 appl_397)
                appl_398 `pseq` kl_declare (ApplC (wrapNamed "dict->" kl_dict_RB)) appl_398) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_399 = Atom Nil
                !appl_400 <- appl_399 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_399
                !appl_401 <- appl_400 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_400
                !appl_402 <- appl_401 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_401
                let !appl_403 = Atom Nil
                !appl_404 <- appl_403 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_403
                !appl_405 <- appl_404 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_404
                !appl_406 <- appl_405 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_405
                let !appl_407 = Atom Nil
                !appl_408 <- appl_406 `pseq` (appl_407 `pseq` klCons appl_406 appl_407)
                !appl_409 <- appl_408 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_408
                !appl_410 <- appl_402 `pseq` (appl_409 `pseq` klCons appl_402 appl_409)
                appl_410 `pseq` kl_declare (ApplC (wrapNamed "dict-rm" kl_dict_rm)) appl_410) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_411 = Atom Nil
                !appl_412 <- appl_411 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_411
                !appl_413 <- appl_412 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_412
                !appl_414 <- appl_413 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_413
                let !appl_415 = Atom Nil
                !appl_416 <- appl_414 `pseq` (appl_415 `pseq` klCons appl_414 appl_415)
                !appl_417 <- appl_416 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_416
                !appl_418 <- appl_417 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_417
                let !appl_419 = Atom Nil
                !appl_420 <- appl_418 `pseq` (appl_419 `pseq` klCons appl_418 appl_419)
                !appl_421 <- appl_420 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_420
                !appl_422 <- appl_421 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_421
                let !appl_423 = Atom Nil
                !appl_424 <- appl_423 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_423
                !appl_425 <- appl_424 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_424
                !appl_426 <- appl_425 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_425
                let !appl_427 = Atom Nil
                !appl_428 <- appl_427 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_427
                !appl_429 <- appl_428 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_428
                !appl_430 <- appl_429 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_429
                let !appl_431 = Atom Nil
                !appl_432 <- appl_430 `pseq` (appl_431 `pseq` klCons appl_430 appl_431)
                !appl_433 <- appl_432 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_432
                !appl_434 <- appl_426 `pseq` (appl_433 `pseq` klCons appl_426 appl_433)
                let !appl_435 = Atom Nil
                !appl_436 <- appl_434 `pseq` (appl_435 `pseq` klCons appl_434 appl_435)
                !appl_437 <- appl_436 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_436
                !appl_438 <- appl_422 `pseq` (appl_437 `pseq` klCons appl_422 appl_437)
                appl_438 `pseq` kl_declare (ApplC (wrapNamed "dict-fold" kl_dict_fold)) appl_438) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_439 = Atom Nil
                !appl_440 <- appl_439 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_439
                !appl_441 <- appl_440 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_440
                !appl_442 <- appl_441 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_441
                let !appl_443 = Atom Nil
                !appl_444 <- appl_443 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_443
                !appl_445 <- appl_444 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_444
                let !appl_446 = Atom Nil
                !appl_447 <- appl_445 `pseq` (appl_446 `pseq` klCons appl_445 appl_446)
                !appl_448 <- appl_447 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_447
                !appl_449 <- appl_442 `pseq` (appl_448 `pseq` klCons appl_442 appl_448)
                appl_449 `pseq` kl_declare (ApplC (wrapNamed "dict-keys" kl_dict_keys)) appl_449) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_450 = Atom Nil
                !appl_451 <- appl_450 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_450
                !appl_452 <- appl_451 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "K")) appl_451
                !appl_453 <- appl_452 `pseq` klCons (ApplC (wrapNamed "dict" kl_dict)) appl_452
                let !appl_454 = Atom Nil
                !appl_455 <- appl_454 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "V")) appl_454
                !appl_456 <- appl_455 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_455
                let !appl_457 = Atom Nil
                !appl_458 <- appl_456 `pseq` (appl_457 `pseq` klCons appl_456 appl_457)
                !appl_459 <- appl_458 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_458
                !appl_460 <- appl_453 `pseq` (appl_459 `pseq` klCons appl_453 appl_459)
                appl_460 `pseq` kl_declare (ApplC (wrapNamed "dict-values" kl_dict_values)) appl_460) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_461 = Atom Nil
                !appl_462 <- appl_461 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_461
                !appl_463 <- appl_462 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_462
                !appl_464 <- appl_463 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_463
                appl_464 `pseq` kl_declare (ApplC (wrapNamed "exit" kl_exit)) appl_464) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_465 = Atom Nil
                !appl_466 <- appl_465 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_465
                !appl_467 <- appl_466 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_466
                !appl_468 <- appl_467 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_467
                appl_468 `pseq` kl_declare (ApplC (wrapNamed "get-time" getTime)) appl_468) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_469 = Atom Nil
                !appl_470 <- appl_469 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_469
                !appl_471 <- appl_470 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_470
                !appl_472 <- appl_471 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_471
                let !appl_473 = Atom Nil
                !appl_474 <- appl_472 `pseq` (appl_473 `pseq` klCons appl_472 appl_473)
                !appl_475 <- appl_474 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_474
                !appl_476 <- appl_475 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_475
                appl_476 `pseq` kl_declare (ApplC (wrapNamed "hash" kl_hash)) appl_476) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_477 = Atom Nil
                !appl_478 <- appl_477 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_477
                !appl_479 <- appl_478 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_478
                let !appl_480 = Atom Nil
                !appl_481 <- appl_480 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_480
                !appl_482 <- appl_481 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_481
                !appl_483 <- appl_479 `pseq` (appl_482 `pseq` klCons appl_479 appl_482)
                appl_483 `pseq` kl_declare (ApplC (wrapNamed "head" kl_head)) appl_483) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_484 = Atom Nil
                !appl_485 <- appl_484 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_484
                !appl_486 <- appl_485 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_485
                let !appl_487 = Atom Nil
                !appl_488 <- appl_487 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_487
                !appl_489 <- appl_488 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_488
                !appl_490 <- appl_486 `pseq` (appl_489 `pseq` klCons appl_486 appl_489)
                appl_490 `pseq` kl_declare (ApplC (wrapNamed "hdv" kl_hdv)) appl_490) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_491 = Atom Nil
                !appl_492 <- appl_491 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_491
                !appl_493 <- appl_492 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_492
                !appl_494 <- appl_493 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_493
                appl_494 `pseq` kl_declare (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_494) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_495 = Atom Nil
                !appl_496 <- appl_495 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_495
                !appl_497 <- appl_496 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_496
                !appl_498 <- appl_497 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_497
                let !appl_499 = Atom Nil
                !appl_500 <- appl_498 `pseq` (appl_499 `pseq` klCons appl_498 appl_499)
                !appl_501 <- appl_500 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_500
                !appl_502 <- appl_501 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_501
                let !appl_503 = Atom Nil
                !appl_504 <- appl_502 `pseq` (appl_503 `pseq` klCons appl_502 appl_503)
                !appl_505 <- appl_504 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_504
                !appl_506 <- appl_505 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_505
                appl_506 `pseq` kl_declare (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_506) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_507 = Atom Nil
                !appl_508 <- appl_507 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_507
                !appl_509 <- appl_508 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_508
                appl_509 `pseq` kl_declare (ApplC (PL "it" kl_it)) appl_509) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_510 = Atom Nil
                !appl_511 <- appl_510 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_510
                !appl_512 <- appl_511 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_511
                appl_512 `pseq` kl_declare (ApplC (PL "implementation" kl_implementation)) appl_512) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_513 = Atom Nil
                !appl_514 <- appl_513 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_513
                !appl_515 <- appl_514 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_514
                let !appl_516 = Atom Nil
                !appl_517 <- appl_516 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_516
                !appl_518 <- appl_517 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_517
                let !appl_519 = Atom Nil
                !appl_520 <- appl_518 `pseq` (appl_519 `pseq` klCons appl_518 appl_519)
                !appl_521 <- appl_520 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_520
                !appl_522 <- appl_515 `pseq` (appl_521 `pseq` klCons appl_515 appl_521)
                appl_522 `pseq` kl_declare (ApplC (wrapNamed "include" kl_include)) appl_522) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_523 = Atom Nil
                !appl_524 <- appl_523 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_523
                !appl_525 <- appl_524 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_524
                let !appl_526 = Atom Nil
                !appl_527 <- appl_526 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_526
                !appl_528 <- appl_527 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_527
                let !appl_529 = Atom Nil
                !appl_530 <- appl_528 `pseq` (appl_529 `pseq` klCons appl_528 appl_529)
                !appl_531 <- appl_530 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_530
                !appl_532 <- appl_525 `pseq` (appl_531 `pseq` klCons appl_525 appl_531)
                appl_532 `pseq` kl_declare (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_532) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_533 = Atom Nil
                !appl_534 <- appl_533 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_533
                !appl_535 <- appl_534 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_534
                appl_535 `pseq` kl_declare (ApplC (PL "inferences" kl_inferences)) appl_535) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_536 = Atom Nil
                !appl_537 <- appl_536 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_536
                !appl_538 <- appl_537 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_537
                !appl_539 <- appl_538 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_538
                let !appl_540 = Atom Nil
                !appl_541 <- appl_539 `pseq` (appl_540 `pseq` klCons appl_539 appl_540)
                !appl_542 <- appl_541 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_541
                !appl_543 <- appl_542 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_542
                appl_543 `pseq` kl_declare (ApplC (wrapNamed "shen.insert" kl_shen_insert)) appl_543) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_544 = Atom Nil
                !appl_545 <- appl_544 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_544
                !appl_546 <- appl_545 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_545
                !appl_547 <- appl_546 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_546
                appl_547 `pseq` kl_declare (ApplC (wrapNamed "integer?" kl_integerP)) appl_547) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_548 = Atom Nil
                !appl_549 <- appl_548 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_548
                !appl_550 <- appl_549 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_549
                let !appl_551 = Atom Nil
                !appl_552 <- appl_550 `pseq` (appl_551 `pseq` klCons appl_550 appl_551)
                !appl_553 <- appl_552 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_552
                !appl_554 <- appl_553 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_553
                appl_554 `pseq` kl_declare (ApplC (wrapNamed "internal" kl_internal)) appl_554) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_555 = Atom Nil
                !appl_556 <- appl_555 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_555
                !appl_557 <- appl_556 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_556
                let !appl_558 = Atom Nil
                !appl_559 <- appl_558 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_558
                !appl_560 <- appl_559 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_559
                let !appl_561 = Atom Nil
                !appl_562 <- appl_561 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_561
                !appl_563 <- appl_562 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_562
                let !appl_564 = Atom Nil
                !appl_565 <- appl_563 `pseq` (appl_564 `pseq` klCons appl_563 appl_564)
                !appl_566 <- appl_565 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_565
                !appl_567 <- appl_560 `pseq` (appl_566 `pseq` klCons appl_560 appl_566)
                let !appl_568 = Atom Nil
                !appl_569 <- appl_567 `pseq` (appl_568 `pseq` klCons appl_567 appl_568)
                !appl_570 <- appl_569 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_569
                !appl_571 <- appl_557 `pseq` (appl_570 `pseq` klCons appl_557 appl_570)
                appl_571 `pseq` kl_declare (ApplC (wrapNamed "intersection" kl_intersection)) appl_571) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_572 = Atom Nil
                !appl_573 <- appl_572 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_572
                !appl_574 <- appl_573 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_573
                appl_574 `pseq` kl_declare (ApplC (PL "kill" kl_kill)) appl_574) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_575 = Atom Nil
                !appl_576 <- appl_575 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_575
                !appl_577 <- appl_576 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_576
                appl_577 `pseq` kl_declare (ApplC (PL "language" kl_language)) appl_577) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_578 = Atom Nil
                !appl_579 <- appl_578 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_578
                !appl_580 <- appl_579 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_579
                let !appl_581 = Atom Nil
                !appl_582 <- appl_581 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_581
                !appl_583 <- appl_582 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_582
                !appl_584 <- appl_580 `pseq` (appl_583 `pseq` klCons appl_580 appl_583)
                appl_584 `pseq` kl_declare (ApplC (wrapNamed "length" kl_length)) appl_584) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_585 = Atom Nil
                !appl_586 <- appl_585 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_585
                !appl_587 <- appl_586 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_586
                let !appl_588 = Atom Nil
                !appl_589 <- appl_588 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_588
                !appl_590 <- appl_589 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_589
                !appl_591 <- appl_587 `pseq` (appl_590 `pseq` klCons appl_587 appl_590)
                appl_591 `pseq` kl_declare (ApplC (wrapNamed "limit" kl_limit)) appl_591) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_592 = Atom Nil
                !appl_593 <- appl_592 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_592
                !appl_594 <- appl_593 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_593
                !appl_595 <- appl_594 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_594
                appl_595 `pseq` kl_declare (ApplC (wrapNamed "load" kl_load)) appl_595) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_596 = Atom Nil
                !appl_597 <- appl_596 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_596
                !appl_598 <- appl_597 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_597
                !appl_599 <- appl_598 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_598
                let !appl_600 = Atom Nil
                !appl_601 <- appl_599 `pseq` (appl_600 `pseq` klCons appl_599 appl_600)
                !appl_602 <- appl_601 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_601
                !appl_603 <- appl_602 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_602
                let !appl_604 = Atom Nil
                !appl_605 <- appl_604 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_604
                !appl_606 <- appl_605 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_605
                let !appl_607 = Atom Nil
                !appl_608 <- appl_607 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_607
                !appl_609 <- appl_608 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_608
                !appl_610 <- appl_606 `pseq` (appl_609 `pseq` klCons appl_606 appl_609)
                let !appl_611 = Atom Nil
                !appl_612 <- appl_610 `pseq` (appl_611 `pseq` klCons appl_610 appl_611)
                !appl_613 <- appl_612 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_612
                !appl_614 <- appl_613 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_613
                let !appl_615 = Atom Nil
                !appl_616 <- appl_614 `pseq` (appl_615 `pseq` klCons appl_614 appl_615)
                !appl_617 <- appl_616 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_616
                !appl_618 <- appl_603 `pseq` (appl_617 `pseq` klCons appl_603 appl_617)
                appl_618 `pseq` kl_declare (ApplC (wrapNamed "fold-left" kl_fold_left)) appl_618) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_619 = Atom Nil
                !appl_620 <- appl_619 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_619
                !appl_621 <- appl_620 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_620
                !appl_622 <- appl_621 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_621
                let !appl_623 = Atom Nil
                !appl_624 <- appl_622 `pseq` (appl_623 `pseq` klCons appl_622 appl_623)
                !appl_625 <- appl_624 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_624
                !appl_626 <- appl_625 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_625
                let !appl_627 = Atom Nil
                !appl_628 <- appl_627 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_627
                !appl_629 <- appl_628 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_628
                let !appl_630 = Atom Nil
                !appl_631 <- appl_630 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_630
                !appl_632 <- appl_631 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_631
                !appl_633 <- appl_632 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_632
                let !appl_634 = Atom Nil
                !appl_635 <- appl_633 `pseq` (appl_634 `pseq` klCons appl_633 appl_634)
                !appl_636 <- appl_635 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_635
                !appl_637 <- appl_629 `pseq` (appl_636 `pseq` klCons appl_629 appl_636)
                let !appl_638 = Atom Nil
                !appl_639 <- appl_637 `pseq` (appl_638 `pseq` klCons appl_637 appl_638)
                !appl_640 <- appl_639 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_639
                !appl_641 <- appl_626 `pseq` (appl_640 `pseq` klCons appl_626 appl_640)
                appl_641 `pseq` kl_declare (ApplC (wrapNamed "fold-right" kl_fold_right)) appl_641) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_642 = Atom Nil
                !appl_643 <- appl_642 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_642
                !appl_644 <- appl_643 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_643
                !appl_645 <- appl_644 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_644
                let !appl_646 = Atom Nil
                !appl_647 <- appl_646 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_646
                !appl_648 <- appl_647 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_647
                let !appl_649 = Atom Nil
                !appl_650 <- appl_649 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_649
                !appl_651 <- appl_650 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_650
                !appl_652 <- appl_648 `pseq` (appl_651 `pseq` klCons appl_648 appl_651)
                let !appl_653 = Atom Nil
                !appl_654 <- appl_652 `pseq` (appl_653 `pseq` klCons appl_652 appl_653)
                !appl_655 <- appl_654 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_654
                !appl_656 <- appl_645 `pseq` (appl_655 `pseq` klCons appl_645 appl_655)
                appl_656 `pseq` kl_declare (ApplC (wrapNamed "for-each" kl_for_each)) appl_656) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_657 = Atom Nil
                !appl_658 <- appl_657 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_657
                !appl_659 <- appl_658 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_658
                !appl_660 <- appl_659 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_659
                let !appl_661 = Atom Nil
                !appl_662 <- appl_661 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_661
                !appl_663 <- appl_662 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_662
                let !appl_664 = Atom Nil
                !appl_665 <- appl_664 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_664
                !appl_666 <- appl_665 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_665
                let !appl_667 = Atom Nil
                !appl_668 <- appl_666 `pseq` (appl_667 `pseq` klCons appl_666 appl_667)
                !appl_669 <- appl_668 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_668
                !appl_670 <- appl_663 `pseq` (appl_669 `pseq` klCons appl_663 appl_669)
                let !appl_671 = Atom Nil
                !appl_672 <- appl_670 `pseq` (appl_671 `pseq` klCons appl_670 appl_671)
                !appl_673 <- appl_672 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_672
                !appl_674 <- appl_660 `pseq` (appl_673 `pseq` klCons appl_660 appl_673)
                appl_674 `pseq` kl_declare (ApplC (wrapNamed "map" kl_map)) appl_674) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_675 = Atom Nil
                !appl_676 <- appl_675 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_675
                !appl_677 <- appl_676 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_676
                let !appl_678 = Atom Nil
                !appl_679 <- appl_677 `pseq` (appl_678 `pseq` klCons appl_677 appl_678)
                !appl_680 <- appl_679 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_679
                !appl_681 <- appl_680 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_680
                let !appl_682 = Atom Nil
                !appl_683 <- appl_682 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_682
                !appl_684 <- appl_683 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_683
                let !appl_685 = Atom Nil
                !appl_686 <- appl_685 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_685
                !appl_687 <- appl_686 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_686
                let !appl_688 = Atom Nil
                !appl_689 <- appl_687 `pseq` (appl_688 `pseq` klCons appl_687 appl_688)
                !appl_690 <- appl_689 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_689
                !appl_691 <- appl_684 `pseq` (appl_690 `pseq` klCons appl_684 appl_690)
                let !appl_692 = Atom Nil
                !appl_693 <- appl_691 `pseq` (appl_692 `pseq` klCons appl_691 appl_692)
                !appl_694 <- appl_693 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_693
                !appl_695 <- appl_681 `pseq` (appl_694 `pseq` klCons appl_681 appl_694)
                appl_695 `pseq` kl_declare (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_695) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_696 = Atom Nil
                !appl_697 <- appl_696 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_696
                !appl_698 <- appl_697 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_697
                !appl_699 <- appl_698 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_698
                let !appl_700 = Atom Nil
                !appl_701 <- appl_700 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_700
                !appl_702 <- appl_701 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_701
                let !appl_703 = Atom Nil
                !appl_704 <- appl_703 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_703
                !appl_705 <- appl_704 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_704
                let !appl_706 = Atom Nil
                !appl_707 <- appl_705 `pseq` (appl_706 `pseq` klCons appl_705 appl_706)
                !appl_708 <- appl_707 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_707
                !appl_709 <- appl_702 `pseq` (appl_708 `pseq` klCons appl_702 appl_708)
                let !appl_710 = Atom Nil
                !appl_711 <- appl_709 `pseq` (appl_710 `pseq` klCons appl_709 appl_710)
                !appl_712 <- appl_711 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_711
                !appl_713 <- appl_699 `pseq` (appl_712 `pseq` klCons appl_699 appl_712)
                appl_713 `pseq` kl_declare (ApplC (wrapNamed "filter" kl_filter)) appl_713) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_714 = Atom Nil
                !appl_715 <- appl_714 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_714
                !appl_716 <- appl_715 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_715
                !appl_717 <- appl_716 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_716
                appl_717 `pseq` kl_declare (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_717) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_718 = Atom Nil
                !appl_719 <- appl_718 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_718
                !appl_720 <- appl_719 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_719
                !appl_721 <- appl_720 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_720
                appl_721 `pseq` kl_declare (ApplC (wrapNamed "n->string" nToString)) appl_721) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_722 = Atom Nil
                !appl_723 <- appl_722 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_722
                !appl_724 <- appl_723 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_723
                !appl_725 <- appl_724 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_724
                appl_725 `pseq` kl_declare (ApplC (wrapNamed "nl" kl_nl)) appl_725) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_726 = Atom Nil
                !appl_727 <- appl_726 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_726
                !appl_728 <- appl_727 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_727
                !appl_729 <- appl_728 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_728
                appl_729 `pseq` kl_declare (ApplC (wrapNamed "not" kl_not)) appl_729) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_730 = Atom Nil
                !appl_731 <- appl_730 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_730
                !appl_732 <- appl_731 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_731
                let !appl_733 = Atom Nil
                !appl_734 <- appl_733 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_733
                !appl_735 <- appl_734 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_734
                !appl_736 <- appl_732 `pseq` (appl_735 `pseq` klCons appl_732 appl_735)
                let !appl_737 = Atom Nil
                !appl_738 <- appl_736 `pseq` (appl_737 `pseq` klCons appl_736 appl_737)
                !appl_739 <- appl_738 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_738
                !appl_740 <- appl_739 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_739
                appl_740 `pseq` kl_declare (ApplC (wrapNamed "nth" kl_nth)) appl_740) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_741 = Atom Nil
                !appl_742 <- appl_741 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_741
                !appl_743 <- appl_742 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_742
                !appl_744 <- appl_743 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_743
                appl_744 `pseq` kl_declare (ApplC (wrapNamed "number?" numberP)) appl_744) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_745 = Atom Nil
                !appl_746 <- appl_745 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_745
                !appl_747 <- appl_746 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_746
                !appl_748 <- appl_747 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_747
                let !appl_749 = Atom Nil
                !appl_750 <- appl_748 `pseq` (appl_749 `pseq` klCons appl_748 appl_749)
                !appl_751 <- appl_750 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_750
                !appl_752 <- appl_751 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_751
                appl_752 `pseq` kl_declare (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_752) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_753 = Atom Nil
                !appl_754 <- appl_753 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_753
                !appl_755 <- appl_754 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_754
                !appl_756 <- appl_755 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_755
                appl_756 `pseq` kl_declare (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_756) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_757 = Atom Nil
                !appl_758 <- appl_757 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_757
                !appl_759 <- appl_758 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_758
                !appl_760 <- appl_759 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_759
                appl_760 `pseq` kl_declare (ApplC (wrapNamed "optimise" kl_optimise)) appl_760) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_761 = Atom Nil
                !appl_762 <- appl_761 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_761
                !appl_763 <- appl_762 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_762
                !appl_764 <- appl_763 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_763
                let !appl_765 = Atom Nil
                !appl_766 <- appl_764 `pseq` (appl_765 `pseq` klCons appl_764 appl_765)
                !appl_767 <- appl_766 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_766
                !appl_768 <- appl_767 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_767
                appl_768 `pseq` kl_declare (Core.Types.Atom (Core.Types.UnboundSym "or")) appl_768) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_769 = Atom Nil
                !appl_770 <- appl_769 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_769
                !appl_771 <- appl_770 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_770
                appl_771 `pseq` kl_declare (ApplC (PL "os" kl_os)) appl_771) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_772 = Atom Nil
                !appl_773 <- appl_772 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_772
                !appl_774 <- appl_773 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_773
                !appl_775 <- appl_774 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_774
                appl_775 `pseq` kl_declare (ApplC (wrapNamed "package?" kl_packageP)) appl_775) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_776 = Atom Nil
                !appl_777 <- appl_776 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_776
                !appl_778 <- appl_777 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_777
                appl_778 `pseq` kl_declare (ApplC (PL "port" kl_port)) appl_778) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_779 = Atom Nil
                !appl_780 <- appl_779 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_779
                !appl_781 <- appl_780 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_780
                appl_781 `pseq` kl_declare (ApplC (PL "porters" kl_porters)) appl_781) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_782 = Atom Nil
                !appl_783 <- appl_782 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_782
                !appl_784 <- appl_783 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_783
                !appl_785 <- appl_784 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_784
                let !appl_786 = Atom Nil
                !appl_787 <- appl_785 `pseq` (appl_786 `pseq` klCons appl_785 appl_786)
                !appl_788 <- appl_787 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_787
                !appl_789 <- appl_788 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_788
                appl_789 `pseq` kl_declare (ApplC (wrapNamed "pos" pos)) appl_789) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_790 = Atom Nil
                !appl_791 <- appl_790 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "out")) appl_790
                !appl_792 <- appl_791 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_791
                let !appl_793 = Atom Nil
                !appl_794 <- appl_793 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_793
                !appl_795 <- appl_794 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_794
                !appl_796 <- appl_792 `pseq` (appl_795 `pseq` klCons appl_792 appl_795)
                let !appl_797 = Atom Nil
                !appl_798 <- appl_796 `pseq` (appl_797 `pseq` klCons appl_796 appl_797)
                !appl_799 <- appl_798 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_798
                !appl_800 <- appl_799 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_799
                appl_800 `pseq` kl_declare (ApplC (wrapNamed "pr" kl_pr)) appl_800) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_801 = Atom Nil
                !appl_802 <- appl_801 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_801
                !appl_803 <- appl_802 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_802
                !appl_804 <- appl_803 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_803
                appl_804 `pseq` kl_declare (ApplC (wrapNamed "print" kl_print)) appl_804) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_805 = Atom Nil
                !appl_806 <- appl_805 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_805
                !appl_807 <- appl_806 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_806
                !appl_808 <- appl_807 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_807
                let !appl_809 = Atom Nil
                !appl_810 <- appl_809 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_809
                !appl_811 <- appl_810 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_810
                !appl_812 <- appl_811 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_811
                let !appl_813 = Atom Nil
                !appl_814 <- appl_812 `pseq` (appl_813 `pseq` klCons appl_812 appl_813)
                !appl_815 <- appl_814 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_814
                !appl_816 <- appl_808 `pseq` (appl_815 `pseq` klCons appl_808 appl_815)
                appl_816 `pseq` kl_declare (ApplC (wrapNamed "profile" kl_profile)) appl_816) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_817 = Atom Nil
                !appl_818 <- appl_817 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_817
                !appl_819 <- appl_818 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_818
                let !appl_820 = Atom Nil
                !appl_821 <- appl_820 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_820
                !appl_822 <- appl_821 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_821
                let !appl_823 = Atom Nil
                !appl_824 <- appl_822 `pseq` (appl_823 `pseq` klCons appl_822 appl_823)
                !appl_825 <- appl_824 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_824
                !appl_826 <- appl_819 `pseq` (appl_825 `pseq` klCons appl_819 appl_825)
                appl_826 `pseq` kl_declare (ApplC (wrapNamed "preclude" kl_preclude)) appl_826) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_827 = Atom Nil
                !appl_828 <- appl_827 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_827
                !appl_829 <- appl_828 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_828
                !appl_830 <- appl_829 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_829
                appl_830 `pseq` kl_declare (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl)) appl_830) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_831 = Atom Nil
                !appl_832 <- appl_831 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_831
                !appl_833 <- appl_832 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_832
                !appl_834 <- appl_833 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_833
                let !appl_835 = Atom Nil
                !appl_836 <- appl_835 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_835
                !appl_837 <- appl_836 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_836
                !appl_838 <- appl_837 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_837
                let !appl_839 = Atom Nil
                !appl_840 <- appl_839 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_839
                !appl_841 <- appl_840 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_840
                !appl_842 <- appl_838 `pseq` (appl_841 `pseq` klCons appl_838 appl_841)
                let !appl_843 = Atom Nil
                !appl_844 <- appl_842 `pseq` (appl_843 `pseq` klCons appl_842 appl_843)
                !appl_845 <- appl_844 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_844
                !appl_846 <- appl_834 `pseq` (appl_845 `pseq` klCons appl_834 appl_845)
                appl_846 `pseq` kl_declare (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_846) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_847 = Atom Nil
                !appl_848 <- appl_847 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_847
                !appl_849 <- appl_848 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_848
                !appl_850 <- appl_849 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_849
                appl_850 `pseq` kl_declare (ApplC (wrapNamed "protect" kl_protect)) appl_850) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_851 = Atom Nil
                !appl_852 <- appl_851 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_851
                !appl_853 <- appl_852 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_852
                let !appl_854 = Atom Nil
                !appl_855 <- appl_854 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_854
                !appl_856 <- appl_855 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_855
                let !appl_857 = Atom Nil
                !appl_858 <- appl_856 `pseq` (appl_857 `pseq` klCons appl_856 appl_857)
                !appl_859 <- appl_858 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_858
                !appl_860 <- appl_853 `pseq` (appl_859 `pseq` klCons appl_853 appl_859)
                appl_860 `pseq` kl_declare (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_860) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_861 = Atom Nil
                !appl_862 <- appl_861 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "out")) appl_861
                !appl_863 <- appl_862 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_862
                let !appl_864 = Atom Nil
                !appl_865 <- appl_864 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_864
                !appl_866 <- appl_865 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_865
                !appl_867 <- appl_863 `pseq` (appl_866 `pseq` klCons appl_863 appl_866)
                let !appl_868 = Atom Nil
                !appl_869 <- appl_867 `pseq` (appl_868 `pseq` klCons appl_867 appl_868)
                !appl_870 <- appl_869 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_869
                !appl_871 <- appl_870 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_870
                appl_871 `pseq` kl_declare (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_871) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_872 = Atom Nil
                !appl_873 <- appl_872 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_872
                !appl_874 <- appl_873 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_873
                let !appl_875 = Atom Nil
                !appl_876 <- appl_874 `pseq` (appl_875 `pseq` klCons appl_874 appl_875)
                !appl_877 <- appl_876 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_876
                !appl_878 <- appl_877 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_877
                appl_878 `pseq` kl_declare (ApplC (wrapNamed "ps" kl_ps)) appl_878) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_879 = Atom Nil
                !appl_880 <- appl_879 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "in")) appl_879
                !appl_881 <- appl_880 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_880
                let !appl_882 = Atom Nil
                !appl_883 <- appl_882 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_882
                !appl_884 <- appl_883 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_883
                !appl_885 <- appl_881 `pseq` (appl_884 `pseq` klCons appl_881 appl_884)
                appl_885 `pseq` kl_declare (ApplC (wrapNamed "read" kl_read)) appl_885) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_886 = Atom Nil
                !appl_887 <- appl_886 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "in")) appl_886
                !appl_888 <- appl_887 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_887
                let !appl_889 = Atom Nil
                !appl_890 <- appl_889 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_889
                !appl_891 <- appl_890 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_890
                !appl_892 <- appl_888 `pseq` (appl_891 `pseq` klCons appl_888 appl_891)
                appl_892 `pseq` kl_declare (ApplC (wrapNamed "read-byte" readByte)) appl_892) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_893 = Atom Nil
                !appl_894 <- appl_893 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "in")) appl_893
                !appl_895 <- appl_894 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_894
                let !appl_896 = Atom Nil
                !appl_897 <- appl_896 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_896
                !appl_898 <- appl_897 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_897
                !appl_899 <- appl_895 `pseq` (appl_898 `pseq` klCons appl_895 appl_898)
                appl_899 `pseq` kl_declare (ApplC (wrapNamed "read-char-code" kl_read_char_code)) appl_899) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_900 = Atom Nil
                !appl_901 <- appl_900 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_900
                !appl_902 <- appl_901 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_901
                let !appl_903 = Atom Nil
                !appl_904 <- appl_902 `pseq` (appl_903 `pseq` klCons appl_902 appl_903)
                !appl_905 <- appl_904 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_904
                !appl_906 <- appl_905 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_905
                appl_906 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-bytelist" kl_read_file_as_bytelist)) appl_906) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_907 = Atom Nil
                !appl_908 <- appl_907 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_907
                !appl_909 <- appl_908 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_908
                let !appl_910 = Atom Nil
                !appl_911 <- appl_909 `pseq` (appl_910 `pseq` klCons appl_909 appl_910)
                !appl_912 <- appl_911 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_911
                !appl_913 <- appl_912 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_912
                appl_913 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-charlist" kl_read_file_as_charlist)) appl_913) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_914 = Atom Nil
                !appl_915 <- appl_914 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_914
                !appl_916 <- appl_915 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_915
                !appl_917 <- appl_916 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_916
                appl_917 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_917) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_918 = Atom Nil
                !appl_919 <- appl_918 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_918
                !appl_920 <- appl_919 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_919
                let !appl_921 = Atom Nil
                !appl_922 <- appl_920 `pseq` (appl_921 `pseq` klCons appl_920 appl_921)
                !appl_923 <- appl_922 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_922
                !appl_924 <- appl_923 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_923
                appl_924 `pseq` kl_declare (ApplC (wrapNamed "read-file" kl_read_file)) appl_924) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_925 = Atom Nil
                !appl_926 <- appl_925 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "unit")) appl_925
                !appl_927 <- appl_926 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_926
                let !appl_928 = Atom Nil
                !appl_929 <- appl_927 `pseq` (appl_928 `pseq` klCons appl_927 appl_928)
                !appl_930 <- appl_929 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_929
                !appl_931 <- appl_930 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_930
                appl_931 `pseq` kl_declare (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_931) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_932 = Atom Nil
                !appl_933 <- appl_932 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_932
                !appl_934 <- appl_933 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_933
                appl_934 `pseq` kl_declare (ApplC (PL "release" kl_release)) appl_934) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_935 = Atom Nil
                !appl_936 <- appl_935 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_935
                !appl_937 <- appl_936 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_936
                let !appl_938 = Atom Nil
                !appl_939 <- appl_938 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_938
                !appl_940 <- appl_939 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_939
                let !appl_941 = Atom Nil
                !appl_942 <- appl_940 `pseq` (appl_941 `pseq` klCons appl_940 appl_941)
                !appl_943 <- appl_942 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_942
                !appl_944 <- appl_937 `pseq` (appl_943 `pseq` klCons appl_937 appl_943)
                let !appl_945 = Atom Nil
                !appl_946 <- appl_944 `pseq` (appl_945 `pseq` klCons appl_944 appl_945)
                !appl_947 <- appl_946 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_946
                !appl_948 <- appl_947 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_947
                appl_948 `pseq` kl_declare (ApplC (wrapNamed "remove" kl_remove)) appl_948) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_949 = Atom Nil
                !appl_950 <- appl_949 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_949
                !appl_951 <- appl_950 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_950
                let !appl_952 = Atom Nil
                !appl_953 <- appl_952 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_952
                !appl_954 <- appl_953 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_953
                let !appl_955 = Atom Nil
                !appl_956 <- appl_954 `pseq` (appl_955 `pseq` klCons appl_954 appl_955)
                !appl_957 <- appl_956 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_956
                !appl_958 <- appl_951 `pseq` (appl_957 `pseq` klCons appl_951 appl_957)
                appl_958 `pseq` kl_declare (ApplC (wrapNamed "reverse" kl_reverse)) appl_958) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_959 = Atom Nil
                !appl_960 <- appl_959 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_959
                !appl_961 <- appl_960 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_960
                !appl_962 <- appl_961 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_961
                appl_962 `pseq` kl_declare (ApplC (wrapNamed "simple-error" simpleError)) appl_962) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_963 = Atom Nil
                !appl_964 <- appl_963 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_963
                !appl_965 <- appl_964 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_964
                !appl_966 <- appl_965 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_965
                let !appl_967 = Atom Nil
                !appl_968 <- appl_967 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_967
                !appl_969 <- appl_968 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_968
                !appl_970 <- appl_966 `pseq` (appl_969 `pseq` klCons appl_966 appl_969)
                appl_970 `pseq` kl_declare (ApplC (wrapNamed "snd" kl_snd)) appl_970) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_971 = Atom Nil
                !appl_972 <- appl_971 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_971
                !appl_973 <- appl_972 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_972
                !appl_974 <- appl_973 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_973
                appl_974 `pseq` kl_declare (ApplC (wrapNamed "specialise" kl_specialise)) appl_974) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_975 = Atom Nil
                !appl_976 <- appl_975 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_975
                !appl_977 <- appl_976 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_976
                !appl_978 <- appl_977 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_977
                appl_978 `pseq` kl_declare (ApplC (wrapNamed "spy" kl_spy)) appl_978) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_979 = Atom Nil
                !appl_980 <- appl_979 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_979
                !appl_981 <- appl_980 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_980
                !appl_982 <- appl_981 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_981
                appl_982 `pseq` kl_declare (ApplC (wrapNamed "step" kl_step)) appl_982) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_983 = Atom Nil
                !appl_984 <- appl_983 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "in")) appl_983
                !appl_985 <- appl_984 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_984
                let !appl_986 = Atom Nil
                !appl_987 <- appl_985 `pseq` (appl_986 `pseq` klCons appl_985 appl_986)
                !appl_988 <- appl_987 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_987
                appl_988 `pseq` kl_declare (ApplC (PL "stinput" kl_stinput)) appl_988) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_989 = Atom Nil
                !appl_990 <- appl_989 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "out")) appl_989
                !appl_991 <- appl_990 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_990
                let !appl_992 = Atom Nil
                !appl_993 <- appl_991 `pseq` (appl_992 `pseq` klCons appl_991 appl_992)
                !appl_994 <- appl_993 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_993
                appl_994 `pseq` kl_declare (ApplC (PL "sterror" kl_sterror)) appl_994) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_995 = Atom Nil
                !appl_996 <- appl_995 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "out")) appl_995
                !appl_997 <- appl_996 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_996
                let !appl_998 = Atom Nil
                !appl_999 <- appl_997 `pseq` (appl_998 `pseq` klCons appl_997 appl_998)
                !appl_1000 <- appl_999 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_999
                appl_1000 `pseq` kl_declare (ApplC (PL "stoutput" kl_stoutput)) appl_1000) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1001 = Atom Nil
                !appl_1002 <- appl_1001 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1001
                !appl_1003 <- appl_1002 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1002
                !appl_1004 <- appl_1003 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1003
                appl_1004 `pseq` kl_declare (ApplC (wrapNamed "string?" stringP)) appl_1004) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1005 = Atom Nil
                !appl_1006 <- appl_1005 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1005
                !appl_1007 <- appl_1006 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1006
                !appl_1008 <- appl_1007 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1007
                appl_1008 `pseq` kl_declare (ApplC (wrapNamed "str" str)) appl_1008) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1009 = Atom Nil
                !appl_1010 <- appl_1009 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1009
                !appl_1011 <- appl_1010 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1010
                !appl_1012 <- appl_1011 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1011
                appl_1012 `pseq` kl_declare (ApplC (wrapNamed "string->n" stringToN)) appl_1012) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1013 = Atom Nil
                !appl_1014 <- appl_1013 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1013
                !appl_1015 <- appl_1014 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1014
                !appl_1016 <- appl_1015 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1015
                appl_1016 `pseq` kl_declare (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_1016) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1017 = Atom Nil
                !appl_1018 <- appl_1017 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1017
                !appl_1019 <- appl_1018 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_1018
                let !appl_1020 = Atom Nil
                !appl_1021 <- appl_1020 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1020
                !appl_1022 <- appl_1021 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1021
                !appl_1023 <- appl_1019 `pseq` (appl_1022 `pseq` klCons appl_1019 appl_1022)
                appl_1023 `pseq` kl_declare (ApplC (wrapNamed "sum" kl_sum)) appl_1023) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1024 = Atom Nil
                !appl_1025 <- appl_1024 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1024
                !appl_1026 <- appl_1025 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1025
                !appl_1027 <- appl_1026 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1026
                appl_1027 `pseq` kl_declare (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_1027) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1028 = Atom Nil
                !appl_1029 <- appl_1028 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1028
                !appl_1030 <- appl_1029 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1029
                !appl_1031 <- appl_1030 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1030
                appl_1031 `pseq` kl_declare (ApplC (wrapNamed "systemf" kl_systemf)) appl_1031) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1032 = Atom Nil
                !appl_1033 <- appl_1032 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1032
                !appl_1034 <- appl_1033 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_1033
                let !appl_1035 = Atom Nil
                !appl_1036 <- appl_1035 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1035
                !appl_1037 <- appl_1036 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_1036
                let !appl_1038 = Atom Nil
                !appl_1039 <- appl_1037 `pseq` (appl_1038 `pseq` klCons appl_1037 appl_1038)
                !appl_1040 <- appl_1039 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1039
                !appl_1041 <- appl_1034 `pseq` (appl_1040 `pseq` klCons appl_1034 appl_1040)
                appl_1041 `pseq` kl_declare (ApplC (wrapNamed "tail" kl_tail)) appl_1041) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1042 = Atom Nil
                !appl_1043 <- appl_1042 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1042
                !appl_1044 <- appl_1043 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1043
                !appl_1045 <- appl_1044 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1044
                appl_1045 `pseq` kl_declare (ApplC (wrapNamed "tlstr" tlstr)) appl_1045) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1046 = Atom Nil
                !appl_1047 <- appl_1046 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1046
                !appl_1048 <- appl_1047 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_1047
                let !appl_1049 = Atom Nil
                !appl_1050 <- appl_1049 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1049
                !appl_1051 <- appl_1050 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_1050
                let !appl_1052 = Atom Nil
                !appl_1053 <- appl_1051 `pseq` (appl_1052 `pseq` klCons appl_1051 appl_1052)
                !appl_1054 <- appl_1053 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1053
                !appl_1055 <- appl_1048 `pseq` (appl_1054 `pseq` klCons appl_1048 appl_1054)
                appl_1055 `pseq` kl_declare (ApplC (wrapNamed "tlv" kl_tlv)) appl_1055) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1056 = Atom Nil
                !appl_1057 <- appl_1056 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1056
                !appl_1058 <- appl_1057 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1057
                !appl_1059 <- appl_1058 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1058
                appl_1059 `pseq` kl_declare (ApplC (wrapNamed "tc" kl_tc)) appl_1059) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1060 = Atom Nil
                !appl_1061 <- appl_1060 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1060
                !appl_1062 <- appl_1061 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1061
                appl_1062 `pseq` kl_declare (ApplC (PL "tc?" kl_tcP)) appl_1062) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1063 = Atom Nil
                !appl_1064 <- appl_1063 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1063
                !appl_1065 <- appl_1064 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lazy")) appl_1064
                let !appl_1066 = Atom Nil
                !appl_1067 <- appl_1066 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1066
                !appl_1068 <- appl_1067 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1067
                !appl_1069 <- appl_1065 `pseq` (appl_1068 `pseq` klCons appl_1065 appl_1068)
                appl_1069 `pseq` kl_declare (ApplC (wrapNamed "thaw" kl_thaw)) appl_1069) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1070 = Atom Nil
                !appl_1071 <- appl_1070 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1070
                !appl_1072 <- appl_1071 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1071
                !appl_1073 <- appl_1072 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1072
                appl_1073 `pseq` kl_declare (ApplC (wrapNamed "track" kl_track)) appl_1073) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1074 = Atom Nil
                !appl_1075 <- appl_1074 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1074
                !appl_1076 <- appl_1075 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1075
                !appl_1077 <- appl_1076 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "exception")) appl_1076
                let !appl_1078 = Atom Nil
                !appl_1079 <- appl_1078 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1078
                !appl_1080 <- appl_1079 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1079
                !appl_1081 <- appl_1077 `pseq` (appl_1080 `pseq` klCons appl_1077 appl_1080)
                let !appl_1082 = Atom Nil
                !appl_1083 <- appl_1081 `pseq` (appl_1082 `pseq` klCons appl_1081 appl_1082)
                !appl_1084 <- appl_1083 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1083
                !appl_1085 <- appl_1084 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1084
                appl_1085 `pseq` kl_declare (Core.Types.Atom (Core.Types.UnboundSym "trap-error")) appl_1085) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1086 = Atom Nil
                !appl_1087 <- appl_1086 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1086
                !appl_1088 <- appl_1087 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1087
                !appl_1089 <- appl_1088 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1088
                appl_1089 `pseq` kl_declare (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_1089) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1090 = Atom Nil
                !appl_1091 <- appl_1090 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1090
                !appl_1092 <- appl_1091 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1091
                !appl_1093 <- appl_1092 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1092
                appl_1093 `pseq` kl_declare (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_1093) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1094 = Atom Nil
                !appl_1095 <- appl_1094 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1094
                !appl_1096 <- appl_1095 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_1095
                let !appl_1097 = Atom Nil
                !appl_1098 <- appl_1097 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1097
                !appl_1099 <- appl_1098 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_1098
                let !appl_1100 = Atom Nil
                !appl_1101 <- appl_1100 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1100
                !appl_1102 <- appl_1101 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "list")) appl_1101
                let !appl_1103 = Atom Nil
                !appl_1104 <- appl_1102 `pseq` (appl_1103 `pseq` klCons appl_1102 appl_1103)
                !appl_1105 <- appl_1104 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1104
                !appl_1106 <- appl_1099 `pseq` (appl_1105 `pseq` klCons appl_1099 appl_1105)
                let !appl_1107 = Atom Nil
                !appl_1108 <- appl_1106 `pseq` (appl_1107 `pseq` klCons appl_1106 appl_1107)
                !appl_1109 <- appl_1108 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1108
                !appl_1110 <- appl_1096 `pseq` (appl_1109 `pseq` klCons appl_1096 appl_1109)
                appl_1110 `pseq` kl_declare (ApplC (wrapNamed "union" kl_union)) appl_1110) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1111 = Atom Nil
                !appl_1112 <- appl_1111 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_1111
                !appl_1113 <- appl_1112 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1112
                !appl_1114 <- appl_1113 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1113
                let !appl_1115 = Atom Nil
                !appl_1116 <- appl_1115 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_1115
                !appl_1117 <- appl_1116 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1116
                !appl_1118 <- appl_1117 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1117
                let !appl_1119 = Atom Nil
                !appl_1120 <- appl_1118 `pseq` (appl_1119 `pseq` klCons appl_1118 appl_1119)
                !appl_1121 <- appl_1120 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1120
                !appl_1122 <- appl_1114 `pseq` (appl_1121 `pseq` klCons appl_1114 appl_1121)
                appl_1122 `pseq` kl_declare (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_1122) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1123 = Atom Nil
                !appl_1124 <- appl_1123 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1123
                !appl_1125 <- appl_1124 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1124
                !appl_1126 <- appl_1125 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1125
                appl_1126 `pseq` kl_declare (ApplC (wrapNamed "untrack" kl_untrack)) appl_1126) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1127 = Atom Nil
                !appl_1128 <- appl_1127 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1127
                !appl_1129 <- appl_1128 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1128
                !appl_1130 <- appl_1129 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "symbol")) appl_1129
                appl_1130 `pseq` kl_declare (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_1130) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1131 = Atom Nil
                !appl_1132 <- appl_1131 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1131
                !appl_1133 <- appl_1132 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1132
                !appl_1134 <- appl_1133 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1133
                appl_1134 `pseq` kl_declare (ApplC (wrapNamed "variable?" kl_variableP)) appl_1134) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1135 = Atom Nil
                !appl_1136 <- appl_1135 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1135
                !appl_1137 <- appl_1136 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1136
                !appl_1138 <- appl_1137 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1137
                appl_1138 `pseq` kl_declare (ApplC (wrapNamed "vector?" kl_vectorP)) appl_1138) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1139 = Atom Nil
                !appl_1140 <- appl_1139 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1139
                !appl_1141 <- appl_1140 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1140
                appl_1141 `pseq` kl_declare (ApplC (PL "version" kl_version)) appl_1141) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1142 = Atom Nil
                !appl_1143 <- appl_1142 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1142
                !appl_1144 <- appl_1143 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1143
                !appl_1145 <- appl_1144 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1144
                let !appl_1146 = Atom Nil
                !appl_1147 <- appl_1145 `pseq` (appl_1146 `pseq` klCons appl_1145 appl_1146)
                !appl_1148 <- appl_1147 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1147
                !appl_1149 <- appl_1148 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1148
                appl_1149 `pseq` kl_declare (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_1149) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1150 = Atom Nil
                !appl_1151 <- appl_1150 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "out")) appl_1150
                !appl_1152 <- appl_1151 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "stream")) appl_1151
                let !appl_1153 = Atom Nil
                !appl_1154 <- appl_1153 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1153
                !appl_1155 <- appl_1154 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1154
                !appl_1156 <- appl_1152 `pseq` (appl_1155 `pseq` klCons appl_1152 appl_1155)
                let !appl_1157 = Atom Nil
                !appl_1158 <- appl_1156 `pseq` (appl_1157 `pseq` klCons appl_1156 appl_1157)
                !appl_1159 <- appl_1158 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1158
                !appl_1160 <- appl_1159 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1159
                appl_1160 `pseq` kl_declare (ApplC (wrapNamed "write-byte" writeByte)) appl_1160) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1161 = Atom Nil
                !appl_1162 <- appl_1161 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1161
                !appl_1163 <- appl_1162 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1162
                !appl_1164 <- appl_1163 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "string")) appl_1163
                appl_1164 `pseq` kl_declare (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_1164) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1165 = Atom Nil
                !appl_1166 <- appl_1165 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1165
                !appl_1167 <- appl_1166 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1166
                !appl_1168 <- appl_1167 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1167
                let !appl_1169 = Atom Nil
                !appl_1170 <- appl_1168 `pseq` (appl_1169 `pseq` klCons appl_1168 appl_1169)
                !appl_1171 <- appl_1170 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1170
                !appl_1172 <- appl_1171 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1171
                appl_1172 `pseq` kl_declare (ApplC (wrapNamed ">" greaterThan)) appl_1172) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1173 = Atom Nil
                !appl_1174 <- appl_1173 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1173
                !appl_1175 <- appl_1174 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1174
                !appl_1176 <- appl_1175 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1175
                let !appl_1177 = Atom Nil
                !appl_1178 <- appl_1176 `pseq` (appl_1177 `pseq` klCons appl_1176 appl_1177)
                !appl_1179 <- appl_1178 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1178
                !appl_1180 <- appl_1179 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1179
                appl_1180 `pseq` kl_declare (ApplC (wrapNamed "<" lessThan)) appl_1180) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1181 = Atom Nil
                !appl_1182 <- appl_1181 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1181
                !appl_1183 <- appl_1182 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1182
                !appl_1184 <- appl_1183 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1183
                let !appl_1185 = Atom Nil
                !appl_1186 <- appl_1184 `pseq` (appl_1185 `pseq` klCons appl_1184 appl_1185)
                !appl_1187 <- appl_1186 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1186
                !appl_1188 <- appl_1187 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1187
                appl_1188 `pseq` kl_declare (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_1188) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1189 = Atom Nil
                !appl_1190 <- appl_1189 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1189
                !appl_1191 <- appl_1190 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1190
                !appl_1192 <- appl_1191 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1191
                let !appl_1193 = Atom Nil
                !appl_1194 <- appl_1192 `pseq` (appl_1193 `pseq` klCons appl_1192 appl_1193)
                !appl_1195 <- appl_1194 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1194
                !appl_1196 <- appl_1195 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1195
                appl_1196 `pseq` kl_declare (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_1196) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1197 = Atom Nil
                !appl_1198 <- appl_1197 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1197
                !appl_1199 <- appl_1198 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1198
                !appl_1200 <- appl_1199 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1199
                let !appl_1201 = Atom Nil
                !appl_1202 <- appl_1200 `pseq` (appl_1201 `pseq` klCons appl_1200 appl_1201)
                !appl_1203 <- appl_1202 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1202
                !appl_1204 <- appl_1203 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1203
                appl_1204 `pseq` kl_declare (ApplC (wrapNamed "=" eq)) appl_1204) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1205 = Atom Nil
                !appl_1206 <- appl_1205 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1205
                !appl_1207 <- appl_1206 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1206
                !appl_1208 <- appl_1207 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1207
                let !appl_1209 = Atom Nil
                !appl_1210 <- appl_1208 `pseq` (appl_1209 `pseq` klCons appl_1208 appl_1209)
                !appl_1211 <- appl_1210 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1210
                !appl_1212 <- appl_1211 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1211
                appl_1212 `pseq` kl_declare (ApplC (wrapNamed "+" add)) appl_1212) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1213 = Atom Nil
                !appl_1214 <- appl_1213 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1213
                !appl_1215 <- appl_1214 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1214
                !appl_1216 <- appl_1215 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1215
                let !appl_1217 = Atom Nil
                !appl_1218 <- appl_1216 `pseq` (appl_1217 `pseq` klCons appl_1216 appl_1217)
                !appl_1219 <- appl_1218 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1218
                !appl_1220 <- appl_1219 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1219
                appl_1220 `pseq` kl_declare (ApplC (wrapNamed "/" divide)) appl_1220) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1221 = Atom Nil
                !appl_1222 <- appl_1221 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1221
                !appl_1223 <- appl_1222 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1222
                !appl_1224 <- appl_1223 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1223
                let !appl_1225 = Atom Nil
                !appl_1226 <- appl_1224 `pseq` (appl_1225 `pseq` klCons appl_1224 appl_1225)
                !appl_1227 <- appl_1226 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1226
                !appl_1228 <- appl_1227 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1227
                appl_1228 `pseq` kl_declare (ApplC (wrapNamed "-" Primitives.subtract)) appl_1228) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1229 = Atom Nil
                !appl_1230 <- appl_1229 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1229
                !appl_1231 <- appl_1230 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1230
                !appl_1232 <- appl_1231 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1231
                let !appl_1233 = Atom Nil
                !appl_1234 <- appl_1232 `pseq` (appl_1233 `pseq` klCons appl_1232 appl_1233)
                !appl_1235 <- appl_1234 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1234
                !appl_1236 <- appl_1235 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "number")) appl_1235
                appl_1236 `pseq` kl_declare (ApplC (wrapNamed "*" multiply)) appl_1236) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
            (do let !appl_1237 = Atom Nil
                !appl_1238 <- appl_1237 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "boolean")) appl_1237
                !appl_1239 <- appl_1238 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1238
                !appl_1240 <- appl_1239 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "B")) appl_1239
                let !appl_1241 = Atom Nil
                !appl_1242 <- appl_1240 `pseq` (appl_1241 `pseq` klCons appl_1240 appl_1241)
                !appl_1243 <- appl_1242 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "-->")) appl_1242
                !appl_1244 <- appl_1243 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "A")) appl_1243
                appl_1244 `pseq` kl_declare (ApplC (wrapNamed "==" kl_EqEq)) appl_1244) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
