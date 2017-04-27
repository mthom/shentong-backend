{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Yacc where

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

kl_shen_yacc :: Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_yacc (!kl_V4140) = do let pat_cond_0 kl_V4140 kl_V4140t kl_V4140th kl_V4140tt = do kl_V4140th `pseq` (kl_V4140tt `pseq` kl_shen_yacc_RBshen kl_V4140th kl_V4140tt)
                                  pat_cond_1 = do do let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                     applyWrapper aw_2 [ApplC (wrapNamed "shen.yacc" kl_shen_yacc)]
                               in case kl_V4140 of
                                      !(kl_V4140@(Cons (Atom (UnboundSym "defcc"))
                                                       (!(kl_V4140t@(Cons (!kl_V4140th)
                                                                          (!kl_V4140tt)))))) -> pat_cond_0 kl_V4140 kl_V4140t kl_V4140th kl_V4140tt
                                      !(kl_V4140@(Cons (ApplC (PL "defcc" _))
                                                       (!(kl_V4140t@(Cons (!kl_V4140th)
                                                                          (!kl_V4140tt)))))) -> pat_cond_0 kl_V4140 kl_V4140t kl_V4140th kl_V4140tt
                                      !(kl_V4140@(Cons (ApplC (Func "defcc" _))
                                                       (!(kl_V4140t@(Cons (!kl_V4140th)
                                                                          (!kl_V4140tt)))))) -> pat_cond_0 kl_V4140 kl_V4140t kl_V4140th kl_V4140tt
                                      _ -> pat_cond_1

kl_shen_yacc_RBshen :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_yacc_RBshen (!kl_V4143) (!kl_V4144) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_CCRules) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_CCBody) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_YaccCases) -> do !appl_3 <- kl_YaccCases `pseq` kl_shen_kill_code kl_YaccCases
                                                                                                                                                                                                                                                        let !appl_4 = Atom Nil
                                                                                                                                                                                                                                                        !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                                                                                                                                                                        !appl_6 <- appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "->")) appl_5
                                                                                                                                                                                                                                                        !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Stream")) appl_6
                                                                                                                                                                                                                                                        !appl_8 <- kl_V4143 `pseq` (appl_7 `pseq` klCons kl_V4143 appl_7)
                                                                                                                                                                                                                                                        appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "define")) appl_8)))
                                                                                                                                                                                    !appl_9 <- kl_CCBody `pseq` kl_shen_yacc_cases kl_CCBody
                                                                                                                                                                                    appl_9 `pseq` applyWrapper appl_2 [appl_9])))
                                                                                                                   let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_cc_body kl_X)))
                                                                                                                   !appl_11 <- appl_10 `pseq` (kl_CCRules `pseq` kl_map appl_10 kl_CCRules)
                                                                                                                   appl_11 `pseq` applyWrapper appl_1 [appl_11])))
                                                 let !appl_12 = Atom Nil
                                                 !appl_13 <- kl_V4144 `pseq` (appl_12 `pseq` kl_shen_split_cc_rules (Atom (B True)) kl_V4144 appl_12)
                                                 appl_13 `pseq` applyWrapper appl_0 [appl_13]

kl_shen_kill_code :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_kill_code (!kl_V4146) = do !appl_0 <- kl_V4146 `pseq` kl_occurrences (ApplC (PL "kill" kl_kill)) kl_V4146
                                   !kl_if_1 <- appl_0 `pseq` greaterThan appl_0 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                   case kl_if_1 of
                                       Atom (B (True)) -> do let !appl_2 = Atom Nil
                                                             !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "E")) appl_2
                                                             !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "shen.analyse-kill" kl_shen_analyse_kill)) appl_3
                                                             let !appl_5 = Atom Nil
                                                             !appl_6 <- appl_4 `pseq` (appl_5 `pseq` klCons appl_4 appl_5)
                                                             !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "E")) appl_6
                                                             !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_7
                                                             let !appl_9 = Atom Nil
                                                             !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                             !appl_11 <- kl_V4146 `pseq` (appl_10 `pseq` klCons kl_V4146 appl_10)
                                                             appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "trap-error")) appl_11
                                       Atom (B (False)) -> do do return kl_V4146
                                       _ -> throwError "if: expected boolean"

kl_kill :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_kill = do simpleError (Core.Types.Atom (Core.Types.Str "yacc kill"))

kl_shen_analyse_kill :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_analyse_kill (!kl_V4148) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let pat_cond_1 = do kl_fail
                                                                                                           pat_cond_2 = do do return kl_V4148
                                                                                                        in case kl_String of
                                                                                                               kl_String@(Atom (Str "yacc kill")) -> pat_cond_1
                                                                                                               _ -> pat_cond_2)))
                                      !appl_3 <- kl_V4148 `pseq` errorToString kl_V4148
                                      appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_split_cc_rules :: Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_split_cc_rules (!kl_V4154) (!kl_V4155) (!kl_V4156) = do let !appl_0 = Atom Nil
                                                                !kl_if_1 <- appl_0 `pseq` (kl_V4155 `pseq` eq appl_0 kl_V4155)
                                                                !kl_if_2 <- case kl_if_1 of
                                                                                Atom (B (True)) -> do let !appl_3 = Atom Nil
                                                                                                      !kl_if_4 <- appl_3 `pseq` (kl_V4156 `pseq` eq appl_3 kl_V4156)
                                                                                                      case kl_if_4 of
                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                          _ -> throwError "if: expected boolean"
                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                _ -> throwError "if: expected boolean"
                                                                case kl_if_2 of
                                                                    Atom (B (True)) -> do return (Atom Nil)
                                                                    Atom (B (False)) -> do let !appl_5 = Atom Nil
                                                                                           !kl_if_6 <- appl_5 `pseq` (kl_V4155 `pseq` eq appl_5 kl_V4155)
                                                                                           case kl_if_6 of
                                                                                               Atom (B (True)) -> do !appl_7 <- kl_V4156 `pseq` kl_reverse kl_V4156
                                                                                                                     let !appl_8 = Atom Nil
                                                                                                                     !appl_9 <- kl_V4154 `pseq` (appl_7 `pseq` (appl_8 `pseq` kl_shen_split_cc_rule kl_V4154 appl_7 appl_8))
                                                                                                                     let !appl_10 = Atom Nil
                                                                                                                     appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                                                               Atom (B (False)) -> do let pat_cond_11 kl_V4155 kl_V4155t = do !appl_12 <- kl_V4156 `pseq` kl_reverse kl_V4156
                                                                                                                                                              let !appl_13 = Atom Nil
                                                                                                                                                              !appl_14 <- kl_V4154 `pseq` (appl_12 `pseq` (appl_13 `pseq` kl_shen_split_cc_rule kl_V4154 appl_12 appl_13))
                                                                                                                                                              let !appl_15 = Atom Nil
                                                                                                                                                              !appl_16 <- kl_V4154 `pseq` (kl_V4155t `pseq` (appl_15 `pseq` kl_shen_split_cc_rules kl_V4154 kl_V4155t appl_15))
                                                                                                                                                              appl_14 `pseq` (appl_16 `pseq` klCons appl_14 appl_16)
                                                                                                                          pat_cond_17 kl_V4155 kl_V4155h kl_V4155t = do !appl_18 <- kl_V4155h `pseq` (kl_V4156 `pseq` klCons kl_V4155h kl_V4156)
                                                                                                                                                                        kl_V4154 `pseq` (kl_V4155t `pseq` (appl_18 `pseq` kl_shen_split_cc_rules kl_V4154 kl_V4155t appl_18))
                                                                                                                          pat_cond_19 = do do let !aw_20 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                              applyWrapper aw_20 [ApplC (wrapNamed "shen.split_cc_rules" kl_shen_split_cc_rules)]
                                                                                                                       in case kl_V4155 of
                                                                                                                              !(kl_V4155@(Cons (Atom (UnboundSym ";"))
                                                                                                                                               (!kl_V4155t))) -> pat_cond_11 kl_V4155 kl_V4155t
                                                                                                                              !(kl_V4155@(Cons (ApplC (PL ";"
                                                                                                                                                          _))
                                                                                                                                               (!kl_V4155t))) -> pat_cond_11 kl_V4155 kl_V4155t
                                                                                                                              !(kl_V4155@(Cons (ApplC (Func ";"
                                                                                                                                                            _))
                                                                                                                                               (!kl_V4155t))) -> pat_cond_11 kl_V4155 kl_V4155t
                                                                                                                              !(kl_V4155@(Cons (!kl_V4155h)
                                                                                                                                               (!kl_V4155t))) -> pat_cond_17 kl_V4155 kl_V4155h kl_V4155t
                                                                                                                              _ -> pat_cond_19
                                                                                               _ -> throwError "if: expected boolean"
                                                                    _ -> throwError "if: expected boolean"

kl_shen_split_cc_rule :: Core.Types.KLValue ->
                         Core.Types.KLValue ->
                         Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_split_cc_rule (!kl_V4164) (!kl_V4165) (!kl_V4166) = do !kl_if_0 <- let pat_cond_1 kl_V4165 kl_V4165h kl_V4165t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V4165t kl_V4165th kl_V4165tt = do let !appl_6 = Atom Nil
                                                                                                                                                                                                                            !kl_if_7 <- appl_6 `pseq` (kl_V4165tt `pseq` eq appl_6 kl_V4165tt)
                                                                                                                                                                                                                            case kl_if_7 of
                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                            pat_cond_8 = do do return (Atom (B False))
                                                                                                                                                                         in case kl_V4165t of
                                                                                                                                                                                !(kl_V4165t@(Cons (!kl_V4165th)
                                                                                                                                                                                                  (!kl_V4165tt))) -> pat_cond_5 kl_V4165t kl_V4165th kl_V4165tt
                                                                                                                                                                                _ -> pat_cond_8
                                                                                                                                                            case kl_if_4 of
                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                            pat_cond_9 = do do return (Atom (B False))
                                                                                                                                         in case kl_V4165h of
                                                                                                                                                kl_V4165h@(Atom (UnboundSym ":=")) -> pat_cond_3
                                                                                                                                                kl_V4165h@(ApplC (PL ":="
                                                                                                                                                                     _)) -> pat_cond_3
                                                                                                                                                kl_V4165h@(ApplC (Func ":="
                                                                                                                                                                       _)) -> pat_cond_3
                                                                                                                                                _ -> pat_cond_9
                                                                                                                            case kl_if_2 of
                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                _ -> throwError "if: expected boolean"
                                                                               pat_cond_10 = do do return (Atom (B False))
                                                                            in case kl_V4165 of
                                                                                   !(kl_V4165@(Cons (!kl_V4165h)
                                                                                                    (!kl_V4165t))) -> pat_cond_1 kl_V4165 kl_V4165h kl_V4165t
                                                                                   _ -> pat_cond_10
                                                               case kl_if_0 of
                                                                   Atom (B (True)) -> do !appl_11 <- kl_V4166 `pseq` kl_reverse kl_V4166
                                                                                         !appl_12 <- kl_V4165 `pseq` tl kl_V4165
                                                                                         appl_11 `pseq` (appl_12 `pseq` klCons appl_11 appl_12)
                                                                   Atom (B (False)) -> do !kl_if_13 <- let pat_cond_14 kl_V4165 kl_V4165h kl_V4165t = do !kl_if_15 <- let pat_cond_16 = do !kl_if_17 <- let pat_cond_18 kl_V4165t kl_V4165th kl_V4165tt = do !kl_if_19 <- let pat_cond_20 kl_V4165tt kl_V4165tth kl_V4165ttt = do !kl_if_21 <- let pat_cond_22 = do !kl_if_23 <- let pat_cond_24 kl_V4165ttt kl_V4165ttth kl_V4165tttt = do let !appl_25 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                                            !kl_if_26 <- appl_25 `pseq` (kl_V4165tttt `pseq` eq appl_25 kl_V4165tttt)
                                                                                                                                                                                                                                                                                                                                                                                                                                            case kl_if_26 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                     pat_cond_27 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                  in case kl_V4165ttt of
                                                                                                                                                                                                                                                                                                                                                                                         !(kl_V4165ttt@(Cons (!kl_V4165ttth)
                                                                                                                                                                                                                                                                                                                                                                                                             (!kl_V4165tttt))) -> pat_cond_24 kl_V4165ttt kl_V4165ttth kl_V4165tttt
                                                                                                                                                                                                                                                                                                                                                                                         _ -> pat_cond_27
                                                                                                                                                                                                                                                                                                                                                                    case kl_if_23 of
                                                                                                                                                                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                   pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                in case kl_V4165tth of
                                                                                                                                                                                                                                                                                                                                                       kl_V4165tth@(Atom (UnboundSym "where")) -> pat_cond_22
                                                                                                                                                                                                                                                                                                                                                       kl_V4165tth@(ApplC (PL "where"
                                                                                                                                                                                                                                                                                                                                                                              _)) -> pat_cond_22
                                                                                                                                                                                                                                                                                                                                                       kl_V4165tth@(ApplC (Func "where"
                                                                                                                                                                                                                                                                                                                                                                                _)) -> pat_cond_22
                                                                                                                                                                                                                                                                                                                                                       _ -> pat_cond_28
                                                                                                                                                                                                                                                                                                                                  case kl_if_21 of
                                                                                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                              pat_cond_29 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                           in case kl_V4165tt of
                                                                                                                                                                                                                                                                                  !(kl_V4165tt@(Cons (!kl_V4165tth)
                                                                                                                                                                                                                                                                                                     (!kl_V4165ttt))) -> pat_cond_20 kl_V4165tt kl_V4165tth kl_V4165ttt
                                                                                                                                                                                                                                                                                  _ -> pat_cond_29
                                                                                                                                                                                                                                                             case kl_if_19 of
                                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                            pat_cond_30 = do do return (Atom (B False))
                                                                                                                                                                                                         in case kl_V4165t of
                                                                                                                                                                                                                !(kl_V4165t@(Cons (!kl_V4165th)
                                                                                                                                                                                                                                  (!kl_V4165tt))) -> pat_cond_18 kl_V4165t kl_V4165th kl_V4165tt
                                                                                                                                                                                                                _ -> pat_cond_30
                                                                                                                                                                                           case kl_if_17 of
                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                          pat_cond_31 = do do return (Atom (B False))
                                                                                                                                                                       in case kl_V4165h of
                                                                                                                                                                              kl_V4165h@(Atom (UnboundSym ":=")) -> pat_cond_16
                                                                                                                                                                              kl_V4165h@(ApplC (PL ":="
                                                                                                                                                                                                   _)) -> pat_cond_16
                                                                                                                                                                              kl_V4165h@(ApplC (Func ":="
                                                                                                                                                                                                     _)) -> pat_cond_16
                                                                                                                                                                              _ -> pat_cond_31
                                                                                                                                                         case kl_if_15 of
                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                           pat_cond_32 = do do return (Atom (B False))
                                                                                                        in case kl_V4165 of
                                                                                                               !(kl_V4165@(Cons (!kl_V4165h)
                                                                                                                                (!kl_V4165t))) -> pat_cond_14 kl_V4165 kl_V4165h kl_V4165t
                                                                                                               _ -> pat_cond_32
                                                                                          case kl_if_13 of
                                                                                              Atom (B (True)) -> do !appl_33 <- kl_V4166 `pseq` kl_reverse kl_V4166
                                                                                                                    !appl_34 <- kl_V4165 `pseq` tl kl_V4165
                                                                                                                    !appl_35 <- appl_34 `pseq` tl appl_34
                                                                                                                    !appl_36 <- appl_35 `pseq` tl appl_35
                                                                                                                    !appl_37 <- appl_36 `pseq` hd appl_36
                                                                                                                    !appl_38 <- kl_V4165 `pseq` tl kl_V4165
                                                                                                                    !appl_39 <- appl_38 `pseq` hd appl_38
                                                                                                                    let !appl_40 = Atom Nil
                                                                                                                    !appl_41 <- appl_39 `pseq` (appl_40 `pseq` klCons appl_39 appl_40)
                                                                                                                    !appl_42 <- appl_37 `pseq` (appl_41 `pseq` klCons appl_37 appl_41)
                                                                                                                    !appl_43 <- appl_42 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "where")) appl_42
                                                                                                                    let !appl_44 = Atom Nil
                                                                                                                    !appl_45 <- appl_43 `pseq` (appl_44 `pseq` klCons appl_43 appl_44)
                                                                                                                    appl_33 `pseq` (appl_45 `pseq` klCons appl_33 appl_45)
                                                                                              Atom (B (False)) -> do let !appl_46 = Atom Nil
                                                                                                                     !kl_if_47 <- appl_46 `pseq` (kl_V4165 `pseq` eq appl_46 kl_V4165)
                                                                                                                     case kl_if_47 of
                                                                                                                         Atom (B (True)) -> do !appl_48 <- kl_V4164 `pseq` (kl_V4166 `pseq` kl_shen_semantic_completion_warning kl_V4164 kl_V4166)
                                                                                                                                               !appl_49 <- kl_V4166 `pseq` kl_reverse kl_V4166
                                                                                                                                               !appl_50 <- appl_49 `pseq` kl_shen_default_semantics appl_49
                                                                                                                                               let !appl_51 = Atom Nil
                                                                                                                                               !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                                                                                                                                               !appl_53 <- appl_52 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ":=")) appl_52
                                                                                                                                               !appl_54 <- kl_V4164 `pseq` (appl_53 `pseq` (kl_V4166 `pseq` kl_shen_split_cc_rule kl_V4164 appl_53 kl_V4166))
                                                                                                                                               appl_48 `pseq` (appl_54 `pseq` kl_do appl_48 appl_54)
                                                                                                                         Atom (B (False)) -> do let pat_cond_55 kl_V4165 kl_V4165h kl_V4165t = do !appl_56 <- kl_V4165h `pseq` (kl_V4166 `pseq` klCons kl_V4165h kl_V4166)
                                                                                                                                                                                                  kl_V4164 `pseq` (kl_V4165t `pseq` (appl_56 `pseq` kl_shen_split_cc_rule kl_V4164 kl_V4165t appl_56))
                                                                                                                                                    pat_cond_57 = do do let !aw_58 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                                                        applyWrapper aw_58 [ApplC (wrapNamed "shen.split_cc_rule" kl_shen_split_cc_rule)]
                                                                                                                                                 in case kl_V4165 of
                                                                                                                                                        !(kl_V4165@(Cons (!kl_V4165h)
                                                                                                                                                                         (!kl_V4165t))) -> pat_cond_55 kl_V4165 kl_V4165h kl_V4165t
                                                                                                                                                        _ -> pat_cond_57
                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                              _ -> throwError "if: expected boolean"
                                                                   _ -> throwError "if: expected boolean"

kl_shen_semantic_completion_warning :: Core.Types.KLValue ->
                                       Core.Types.KLValue ->
                                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_semantic_completion_warning (!kl_V4177) (!kl_V4178) = do let pat_cond_0 = do !appl_1 <- kl_stoutput
                                                                                     let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                     !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [Core.Types.Atom (Core.Types.Str "warning: "),
                                                                                                                                 appl_1]
                                                                                     let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                 !appl_6 <- kl_X `pseq` applyWrapper aw_5 [kl_X,
                                                                                                                                                                                           Core.Types.Atom (Core.Types.Str " "),
                                                                                                                                                                                           Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                                                                                                 !appl_7 <- kl_stoutput
                                                                                                                                                 let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                                                 appl_6 `pseq` (appl_7 `pseq` applyWrapper aw_8 [appl_6,
                                                                                                                                                                                                 appl_7]))))
                                                                                     !appl_9 <- kl_V4178 `pseq` kl_reverse kl_V4178
                                                                                     !appl_10 <- appl_4 `pseq` (appl_9 `pseq` kl_for_each appl_4 appl_9)
                                                                                     !appl_11 <- kl_stoutput
                                                                                     let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                     !appl_13 <- appl_11 `pseq` applyWrapper aw_12 [Core.Types.Atom (Core.Types.Str "has no semantics.\n"),
                                                                                                                                    appl_11]
                                                                                     !appl_14 <- appl_10 `pseq` (appl_13 `pseq` kl_do appl_10 appl_13)
                                                                                     appl_3 `pseq` (appl_14 `pseq` kl_do appl_3 appl_14)
                                                                     pat_cond_15 = do do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                                                                  in case kl_V4177 of
                                                                         kl_V4177@(Atom (UnboundSym "true")) -> pat_cond_0
                                                                         kl_V4177@(Atom (B (True))) -> pat_cond_0
                                                                         _ -> pat_cond_15

kl_shen_default_semantics :: Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_default_semantics (!kl_V4180) = do let !appl_0 = Atom Nil
                                           !kl_if_1 <- appl_0 `pseq` (kl_V4180 `pseq` eq appl_0 kl_V4180)
                                           case kl_if_1 of
                                               Atom (B (True)) -> do return (Atom Nil)
                                               Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V4180 kl_V4180h kl_V4180t = do let !appl_4 = Atom Nil
                                                                                                                                   !kl_if_5 <- appl_4 `pseq` (kl_V4180t `pseq` eq appl_4 kl_V4180t)
                                                                                                                                   !kl_if_6 <- case kl_if_5 of
                                                                                                                                                   Atom (B (True)) -> do !kl_if_7 <- kl_V4180h `pseq` kl_shen_grammar_symbolP kl_V4180h
                                                                                                                                                                         case kl_if_7 of
                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                   case kl_if_6 of
                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                      pat_cond_8 = do do return (Atom (B False))
                                                                                   in case kl_V4180 of
                                                                                          !(kl_V4180@(Cons (!kl_V4180h)
                                                                                                           (!kl_V4180t))) -> pat_cond_3 kl_V4180 kl_V4180h kl_V4180t
                                                                                          _ -> pat_cond_8
                                                                      case kl_if_2 of
                                                                          Atom (B (True)) -> do kl_V4180 `pseq` hd kl_V4180
                                                                          Atom (B (False)) -> do !kl_if_9 <- let pat_cond_10 kl_V4180 kl_V4180h kl_V4180t = do !kl_if_11 <- kl_V4180h `pseq` kl_shen_grammar_symbolP kl_V4180h
                                                                                                                                                               case kl_if_11 of
                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                 pat_cond_12 = do do return (Atom (B False))
                                                                                                              in case kl_V4180 of
                                                                                                                     !(kl_V4180@(Cons (!kl_V4180h)
                                                                                                                                      (!kl_V4180t))) -> pat_cond_10 kl_V4180 kl_V4180h kl_V4180t
                                                                                                                     _ -> pat_cond_12
                                                                                                 case kl_if_9 of
                                                                                                     Atom (B (True)) -> do !appl_13 <- kl_V4180 `pseq` hd kl_V4180
                                                                                                                           !appl_14 <- kl_V4180 `pseq` tl kl_V4180
                                                                                                                           !appl_15 <- appl_14 `pseq` kl_shen_default_semantics appl_14
                                                                                                                           let !appl_16 = Atom Nil
                                                                                                                           !appl_17 <- appl_15 `pseq` (appl_16 `pseq` klCons appl_15 appl_16)
                                                                                                                           !appl_18 <- appl_13 `pseq` (appl_17 `pseq` klCons appl_13 appl_17)
                                                                                                                           appl_18 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_18
                                                                                                     Atom (B (False)) -> do let pat_cond_19 kl_V4180 kl_V4180h kl_V4180t = do !appl_20 <- kl_V4180t `pseq` kl_shen_default_semantics kl_V4180t
                                                                                                                                                                              let !appl_21 = Atom Nil
                                                                                                                                                                              !appl_22 <- appl_20 `pseq` (appl_21 `pseq` klCons appl_20 appl_21)
                                                                                                                                                                              !appl_23 <- kl_V4180h `pseq` (appl_22 `pseq` klCons kl_V4180h appl_22)
                                                                                                                                                                              appl_23 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_23
                                                                                                                                pat_cond_24 = do do let !aw_25 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                                    applyWrapper aw_25 [ApplC (wrapNamed "shen.default_semantics" kl_shen_default_semantics)]
                                                                                                                             in case kl_V4180 of
                                                                                                                                    !(kl_V4180@(Cons (!kl_V4180h)
                                                                                                                                                     (!kl_V4180t))) -> pat_cond_19 kl_V4180 kl_V4180h kl_V4180t
                                                                                                                                    _ -> pat_cond_24
                                                                                                     _ -> throwError "if: expected boolean"
                                                                          _ -> throwError "if: expected boolean"
                                               _ -> throwError "if: expected boolean"

kl_shen_grammar_symbolP :: Core.Types.KLValue ->
                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_grammar_symbolP (!kl_V4182) = do !kl_if_0 <- kl_V4182 `pseq` kl_symbolP kl_V4182
                                         case kl_if_0 of
                                             Atom (B (True)) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Cs) -> do !appl_2 <- kl_Cs `pseq` hd kl_Cs
                                                                                                                                !kl_if_3 <- appl_2 `pseq` eq appl_2 (Core.Types.Atom (Core.Types.Str "<"))
                                                                                                                                case kl_if_3 of
                                                                                                                                    Atom (B (True)) -> do !appl_4 <- kl_Cs `pseq` kl_reverse kl_Cs
                                                                                                                                                          !appl_5 <- appl_4 `pseq` hd appl_4
                                                                                                                                                          !kl_if_6 <- appl_5 `pseq` eq appl_5 (Core.Types.Atom (Core.Types.Str ">"))
                                                                                                                                                          case kl_if_6 of
                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                    _ -> throwError "if: expected boolean")))
                                                                   !appl_7 <- kl_V4182 `pseq` kl_explode kl_V4182
                                                                   !appl_8 <- appl_7 `pseq` kl_shen_strip_pathname appl_7
                                                                   !kl_if_9 <- appl_8 `pseq` applyWrapper appl_1 [appl_8]
                                                                   case kl_if_9 of
                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                       _ -> throwError "if: expected boolean"
                                             Atom (B (False)) -> do do return (Atom (B False))
                                             _ -> throwError "if: expected boolean"

kl_shen_yacc_cases :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_yacc_cases (!kl_V4184) = do !kl_if_0 <- let pat_cond_1 kl_V4184 kl_V4184h kl_V4184t = do let !appl_2 = Atom Nil
                                                                                                 !kl_if_3 <- appl_2 `pseq` (kl_V4184t `pseq` eq appl_2 kl_V4184t)
                                                                                                 case kl_if_3 of
                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                     _ -> throwError "if: expected boolean"
                                                    pat_cond_4 = do do return (Atom (B False))
                                                 in case kl_V4184 of
                                                        !(kl_V4184@(Cons (!kl_V4184h)
                                                                         (!kl_V4184t))) -> pat_cond_1 kl_V4184 kl_V4184h kl_V4184t
                                                        _ -> pat_cond_4
                                    case kl_if_0 of
                                        Atom (B (True)) -> do kl_V4184 `pseq` hd kl_V4184
                                        Atom (B (False)) -> do let pat_cond_5 kl_V4184 kl_V4184h kl_V4184t = do let !appl_6 = ApplC (Func "lambda" (Context (\(!kl_P) -> do let !appl_7 = Atom Nil
                                                                                                                                                                            !appl_8 <- appl_7 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_7
                                                                                                                                                                            let !appl_9 = Atom Nil
                                                                                                                                                                            !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                                                                                                                                            !appl_11 <- kl_P `pseq` (appl_10 `pseq` klCons kl_P appl_10)
                                                                                                                                                                            !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_11
                                                                                                                                                                            !appl_13 <- kl_V4184t `pseq` kl_shen_yacc_cases kl_V4184t
                                                                                                                                                                            let !appl_14 = Atom Nil
                                                                                                                                                                            !appl_15 <- kl_P `pseq` (appl_14 `pseq` klCons kl_P appl_14)
                                                                                                                                                                            !appl_16 <- appl_13 `pseq` (appl_15 `pseq` klCons appl_13 appl_15)
                                                                                                                                                                            !appl_17 <- appl_12 `pseq` (appl_16 `pseq` klCons appl_12 appl_16)
                                                                                                                                                                            !appl_18 <- appl_17 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_17
                                                                                                                                                                            let !appl_19 = Atom Nil
                                                                                                                                                                            !appl_20 <- appl_18 `pseq` (appl_19 `pseq` klCons appl_18 appl_19)
                                                                                                                                                                            !appl_21 <- kl_V4184h `pseq` (appl_20 `pseq` klCons kl_V4184h appl_20)
                                                                                                                                                                            !appl_22 <- kl_P `pseq` (appl_21 `pseq` klCons kl_P appl_21)
                                                                                                                                                                            appl_22 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_22)))
                                                                                                                applyWrapper appl_6 [Core.Types.Atom (Core.Types.UnboundSym "YaccParse")]
                                                                   pat_cond_23 = do do let !aw_24 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                       applyWrapper aw_24 [ApplC (wrapNamed "shen.yacc_cases" kl_shen_yacc_cases)]
                                                                in case kl_V4184 of
                                                                       !(kl_V4184@(Cons (!kl_V4184h)
                                                                                        (!kl_V4184t))) -> pat_cond_5 kl_V4184 kl_V4184h kl_V4184t
                                                                       _ -> pat_cond_23
                                        _ -> throwError "if: expected boolean"

kl_shen_cc_body :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_cc_body (!kl_V4186) = do !kl_if_0 <- let pat_cond_1 kl_V4186 kl_V4186h kl_V4186t = do !kl_if_2 <- let pat_cond_3 kl_V4186t kl_V4186th kl_V4186tt = do let !appl_4 = Atom Nil
                                                                                                                                                              !kl_if_5 <- appl_4 `pseq` (kl_V4186tt `pseq` eq appl_4 kl_V4186tt)
                                                                                                                                                              case kl_if_5 of
                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                              pat_cond_6 = do do return (Atom (B False))
                                                                                                           in case kl_V4186t of
                                                                                                                  !(kl_V4186t@(Cons (!kl_V4186th)
                                                                                                                                    (!kl_V4186tt))) -> pat_cond_3 kl_V4186t kl_V4186th kl_V4186tt
                                                                                                                  _ -> pat_cond_6
                                                                                              case kl_if_2 of
                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                  _ -> throwError "if: expected boolean"
                                                 pat_cond_7 = do do return (Atom (B False))
                                              in case kl_V4186 of
                                                     !(kl_V4186@(Cons (!kl_V4186h)
                                                                      (!kl_V4186t))) -> pat_cond_1 kl_V4186 kl_V4186h kl_V4186t
                                                     _ -> pat_cond_7
                                 case kl_if_0 of
                                     Atom (B (True)) -> do !appl_8 <- kl_V4186 `pseq` hd kl_V4186
                                                           !appl_9 <- kl_V4186 `pseq` tl kl_V4186
                                                           !appl_10 <- appl_9 `pseq` hd appl_9
                                                           appl_8 `pseq` (appl_10 `pseq` kl_shen_syntax appl_8 (Core.Types.Atom (Core.Types.UnboundSym "Stream")) appl_10)
                                     Atom (B (False)) -> do do let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                               applyWrapper aw_11 [ApplC (wrapNamed "shen.cc_body" kl_shen_cc_body)]
                                     _ -> throwError "if: expected boolean"

kl_shen_syntax :: Core.Types.KLValue ->
                  Core.Types.KLValue ->
                  Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_syntax (!kl_V4190) (!kl_V4191) (!kl_V4192) = do let !appl_0 = Atom Nil
                                                        !kl_if_1 <- appl_0 `pseq` (kl_V4190 `pseq` eq appl_0 kl_V4190)
                                                        !kl_if_2 <- case kl_if_1 of
                                                                        Atom (B (True)) -> do !kl_if_3 <- let pat_cond_4 kl_V4192 kl_V4192h kl_V4192t = do !kl_if_5 <- let pat_cond_6 = do !kl_if_7 <- let pat_cond_8 kl_V4192t kl_V4192th kl_V4192tt = do !kl_if_9 <- let pat_cond_10 kl_V4192tt kl_V4192tth kl_V4192ttt = do let !appl_11 = Atom Nil
                                                                                                                                                                                                                                                                                                                               !kl_if_12 <- appl_11 `pseq` (kl_V4192ttt `pseq` eq appl_11 kl_V4192ttt)
                                                                                                                                                                                                                                                                                                                               case kl_if_12 of
                                                                                                                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                           pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                        in case kl_V4192tt of
                                                                                                                                                                                                                                                                               !(kl_V4192tt@(Cons (!kl_V4192tth)
                                                                                                                                                                                                                                                                                                  (!kl_V4192ttt))) -> pat_cond_10 kl_V4192tt kl_V4192tth kl_V4192ttt
                                                                                                                                                                                                                                                                               _ -> pat_cond_13
                                                                                                                                                                                                                                                           case kl_if_9 of
                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                           pat_cond_14 = do do return (Atom (B False))
                                                                                                                                                                                                        in case kl_V4192t of
                                                                                                                                                                                                               !(kl_V4192t@(Cons (!kl_V4192th)
                                                                                                                                                                                                                                 (!kl_V4192tt))) -> pat_cond_8 kl_V4192t kl_V4192th kl_V4192tt
                                                                                                                                                                                                               _ -> pat_cond_14
                                                                                                                                                                                           case kl_if_7 of
                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                           pat_cond_15 = do do return (Atom (B False))
                                                                                                                                                                        in case kl_V4192h of
                                                                                                                                                                               kl_V4192h@(Atom (UnboundSym "where")) -> pat_cond_6
                                                                                                                                                                               kl_V4192h@(ApplC (PL "where"
                                                                                                                                                                                                    _)) -> pat_cond_6
                                                                                                                                                                               kl_V4192h@(ApplC (Func "where"
                                                                                                                                                                                                      _)) -> pat_cond_6
                                                                                                                                                                               _ -> pat_cond_15
                                                                                                                                                           case kl_if_5 of
                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                              pat_cond_16 = do do return (Atom (B False))
                                                                                                           in case kl_V4192 of
                                                                                                                  !(kl_V4192@(Cons (!kl_V4192h)
                                                                                                                                   (!kl_V4192t))) -> pat_cond_4 kl_V4192 kl_V4192h kl_V4192t
                                                                                                                  _ -> pat_cond_16
                                                                                              case kl_if_3 of
                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                  _ -> throwError "if: expected boolean"
                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                        _ -> throwError "if: expected boolean"
                                                        case kl_if_2 of
                                                            Atom (B (True)) -> do !appl_17 <- kl_V4192 `pseq` tl kl_V4192
                                                                                  !appl_18 <- appl_17 `pseq` hd appl_17
                                                                                  !appl_19 <- appl_18 `pseq` kl_shen_semantics appl_18
                                                                                  let !appl_20 = Atom Nil
                                                                                  !appl_21 <- kl_V4191 `pseq` (appl_20 `pseq` klCons kl_V4191 appl_20)
                                                                                  !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_21
                                                                                  !appl_23 <- kl_V4192 `pseq` tl kl_V4192
                                                                                  !appl_24 <- appl_23 `pseq` tl appl_23
                                                                                  !appl_25 <- appl_24 `pseq` hd appl_24
                                                                                  !appl_26 <- appl_25 `pseq` kl_shen_semantics appl_25
                                                                                  let !appl_27 = Atom Nil
                                                                                  !appl_28 <- appl_26 `pseq` (appl_27 `pseq` klCons appl_26 appl_27)
                                                                                  !appl_29 <- appl_22 `pseq` (appl_28 `pseq` klCons appl_22 appl_28)
                                                                                  !appl_30 <- appl_29 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_29
                                                                                  let !appl_31 = Atom Nil
                                                                                  !appl_32 <- appl_31 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_31
                                                                                  let !appl_33 = Atom Nil
                                                                                  !appl_34 <- appl_32 `pseq` (appl_33 `pseq` klCons appl_32 appl_33)
                                                                                  !appl_35 <- appl_30 `pseq` (appl_34 `pseq` klCons appl_30 appl_34)
                                                                                  !appl_36 <- appl_19 `pseq` (appl_35 `pseq` klCons appl_19 appl_35)
                                                                                  appl_36 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_36
                                                            Atom (B (False)) -> do let !appl_37 = Atom Nil
                                                                                   !kl_if_38 <- appl_37 `pseq` (kl_V4190 `pseq` eq appl_37 kl_V4190)
                                                                                   case kl_if_38 of
                                                                                       Atom (B (True)) -> do let !appl_39 = Atom Nil
                                                                                                             !appl_40 <- kl_V4191 `pseq` (appl_39 `pseq` klCons kl_V4191 appl_39)
                                                                                                             !appl_41 <- appl_40 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_40
                                                                                                             !appl_42 <- kl_V4192 `pseq` kl_shen_semantics kl_V4192
                                                                                                             let !appl_43 = Atom Nil
                                                                                                             !appl_44 <- appl_42 `pseq` (appl_43 `pseq` klCons appl_42 appl_43)
                                                                                                             !appl_45 <- appl_41 `pseq` (appl_44 `pseq` klCons appl_41 appl_44)
                                                                                                             appl_45 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_45
                                                                                       Atom (B (False)) -> do let pat_cond_46 kl_V4190 kl_V4190h kl_V4190t = do !kl_if_47 <- kl_V4190h `pseq` kl_shen_grammar_symbolP kl_V4190h
                                                                                                                                                                case kl_if_47 of
                                                                                                                                                                    Atom (B (True)) -> do kl_V4190 `pseq` (kl_V4191 `pseq` (kl_V4192 `pseq` kl_shen_recursive_descent kl_V4190 kl_V4191 kl_V4192))
                                                                                                                                                                    Atom (B (False)) -> do do !kl_if_48 <- kl_V4190h `pseq` kl_variableP kl_V4190h
                                                                                                                                                                                              case kl_if_48 of
                                                                                                                                                                                                  Atom (B (True)) -> do kl_V4190 `pseq` (kl_V4191 `pseq` (kl_V4192 `pseq` kl_shen_variable_match kl_V4190 kl_V4191 kl_V4192))
                                                                                                                                                                                                  Atom (B (False)) -> do do !kl_if_49 <- kl_V4190h `pseq` kl_shen_jump_streamP kl_V4190h
                                                                                                                                                                                                                            case kl_if_49 of
                                                                                                                                                                                                                                Atom (B (True)) -> do kl_V4190 `pseq` (kl_V4191 `pseq` (kl_V4192 `pseq` kl_shen_jump_stream kl_V4190 kl_V4191 kl_V4192))
                                                                                                                                                                                                                                Atom (B (False)) -> do do !kl_if_50 <- kl_V4190h `pseq` kl_shen_terminalP kl_V4190h
                                                                                                                                                                                                                                                          case kl_if_50 of
                                                                                                                                                                                                                                                              Atom (B (True)) -> do kl_V4190 `pseq` (kl_V4191 `pseq` (kl_V4192 `pseq` kl_shen_check_stream kl_V4190 kl_V4191 kl_V4192))
                                                                                                                                                                                                                                                              Atom (B (False)) -> do do let pat_cond_51 kl_V4190h kl_V4190hh kl_V4190ht = do !appl_52 <- kl_V4190h `pseq` kl_shen_decons kl_V4190h
                                                                                                                                                                                                                                                                                                                                             appl_52 `pseq` (kl_V4190t `pseq` (kl_V4191 `pseq` (kl_V4192 `pseq` kl_shen_list_stream appl_52 kl_V4190t kl_V4191 kl_V4192)))
                                                                                                                                                                                                                                                                                            pat_cond_53 = do do let !aw_54 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                                                !appl_55 <- kl_V4190h `pseq` applyWrapper aw_54 [kl_V4190h,
                                                                                                                                                                                                                                                                                                                                                                 Core.Types.Atom (Core.Types.Str " is not legal syntax\n"),
                                                                                                                                                                                                                                                                                                                                                                 Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                                                                                                                                                                                                                                                                appl_55 `pseq` simpleError appl_55
                                                                                                                                                                                                                                                                                         in case kl_V4190h of
                                                                                                                                                                                                                                                                                                !(kl_V4190h@(Cons (!kl_V4190hh)
                                                                                                                                                                                                                                                                                                                  (!kl_V4190ht))) -> pat_cond_51 kl_V4190h kl_V4190hh kl_V4190ht
                                                                                                                                                                                                                                                                                                _ -> pat_cond_53
                                                                                                                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                  pat_cond_56 = do do let !aw_57 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                      applyWrapper aw_57 [ApplC (wrapNamed "shen.syntax" kl_shen_syntax)]
                                                                                                               in case kl_V4190 of
                                                                                                                      !(kl_V4190@(Cons (!kl_V4190h)
                                                                                                                                       (!kl_V4190t))) -> pat_cond_46 kl_V4190 kl_V4190h kl_V4190t
                                                                                                                      _ -> pat_cond_56
                                                                                       _ -> throwError "if: expected boolean"
                                                            _ -> throwError "if: expected boolean"

kl_shen_list_stream :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_list_stream (!kl_V4197) (!kl_V4198) (!kl_V4199) (!kl_V4200) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Placeholder) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_RunOn) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_4 = Atom Nil
                                                                                                                                                                                                                                                                                                                                               !appl_5 <- appl_4 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_4
                                                                                                                                                                                                                                                                                                                                               let !appl_6 = Atom Nil
                                                                                                                                                                                                                                                                                                                                               !appl_7 <- appl_5 `pseq` (appl_6 `pseq` klCons appl_5 appl_6)
                                                                                                                                                                                                                                                                                                                                               !appl_8 <- kl_Action `pseq` (appl_7 `pseq` klCons kl_Action appl_7)
                                                                                                                                                                                                                                                                                                                                               !appl_9 <- kl_Test `pseq` (appl_8 `pseq` klCons kl_Test appl_8)
                                                                                                                                                                                                                                                                                                                                               appl_9 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_9)))
                                                                                                                                                                                                                                                                              let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                              !appl_11 <- kl_V4199 `pseq` (appl_10 `pseq` klCons kl_V4199 appl_10)
                                                                                                                                                                                                                                                                              !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_11
                                                                                                                                                                                                                                                                              let !appl_13 = Atom Nil
                                                                                                                                                                                                                                                                              !appl_14 <- appl_12 `pseq` (appl_13 `pseq` klCons appl_12 appl_13)
                                                                                                                                                                                                                                                                              !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_14
                                                                                                                                                                                                                                                                              let !appl_16 = Atom Nil
                                                                                                                                                                                                                                                                              !appl_17 <- kl_V4199 `pseq` (appl_16 `pseq` klCons kl_V4199 appl_16)
                                                                                                                                                                                                                                                                              !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_17
                                                                                                                                                                                                                                                                              let !appl_19 = Atom Nil
                                                                                                                                                                                                                                                                              !appl_20 <- appl_18 `pseq` (appl_19 `pseq` klCons appl_18 appl_19)
                                                                                                                                                                                                                                                                              !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_20
                                                                                                                                                                                                                                                                              let !appl_22 = Atom Nil
                                                                                                                                                                                                                                                                              !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                                                                                                                                                                                                                                                                              !appl_24 <- appl_15 `pseq` (appl_23 `pseq` klCons appl_15 appl_23)
                                                                                                                                                                                                                                                                              !appl_25 <- appl_24 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_24
                                                                                                                                                                                                                                                                              !appl_26 <- kl_V4197 `pseq` (appl_25 `pseq` (kl_Placeholder `pseq` kl_shen_syntax kl_V4197 appl_25 kl_Placeholder))
                                                                                                                                                                                                                                                                              !appl_27 <- kl_RunOn `pseq` (kl_Placeholder `pseq` (appl_26 `pseq` kl_shen_insert_runon kl_RunOn kl_Placeholder appl_26))
                                                                                                                                                                                                                                                                              appl_27 `pseq` applyWrapper appl_3 [appl_27])))
                                                                                                                                                                                                              let !appl_28 = Atom Nil
                                                                                                                                                                                                              !appl_29 <- kl_V4199 `pseq` (appl_28 `pseq` klCons kl_V4199 appl_28)
                                                                                                                                                                                                              !appl_30 <- appl_29 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_29
                                                                                                                                                                                                              let !appl_31 = Atom Nil
                                                                                                                                                                                                              !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                                                                                                                                                              !appl_33 <- appl_32 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_32
                                                                                                                                                                                                              let !appl_34 = Atom Nil
                                                                                                                                                                                                              !appl_35 <- kl_V4199 `pseq` (appl_34 `pseq` klCons kl_V4199 appl_34)
                                                                                                                                                                                                              !appl_36 <- appl_35 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_35
                                                                                                                                                                                                              let !appl_37 = Atom Nil
                                                                                                                                                                                                              !appl_38 <- appl_36 `pseq` (appl_37 `pseq` klCons appl_36 appl_37)
                                                                                                                                                                                                              !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_38
                                                                                                                                                                                                              let !appl_40 = Atom Nil
                                                                                                                                                                                                              !appl_41 <- appl_39 `pseq` (appl_40 `pseq` klCons appl_39 appl_40)
                                                                                                                                                                                                              !appl_42 <- appl_33 `pseq` (appl_41 `pseq` klCons appl_33 appl_41)
                                                                                                                                                                                                              !appl_43 <- appl_42 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_42
                                                                                                                                                                                                              !appl_44 <- kl_V4198 `pseq` (appl_43 `pseq` (kl_V4200 `pseq` kl_shen_syntax kl_V4198 appl_43 kl_V4200))
                                                                                                                                                                                                              appl_44 `pseq` applyWrapper appl_2 [appl_44])))
                                                                                                                                        !appl_45 <- kl_gensym (Core.Types.Atom (Core.Types.UnboundSym "shen.place"))
                                                                                                                                        appl_45 `pseq` applyWrapper appl_1 [appl_45])))
                                                                         let !appl_46 = Atom Nil
                                                                         !appl_47 <- kl_V4199 `pseq` (appl_46 `pseq` klCons kl_V4199 appl_46)
                                                                         !appl_48 <- appl_47 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_47
                                                                         let !appl_49 = Atom Nil
                                                                         !appl_50 <- appl_48 `pseq` (appl_49 `pseq` klCons appl_48 appl_49)
                                                                         !appl_51 <- appl_50 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_50
                                                                         let !appl_52 = Atom Nil
                                                                         !appl_53 <- kl_V4199 `pseq` (appl_52 `pseq` klCons kl_V4199 appl_52)
                                                                         !appl_54 <- appl_53 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_53
                                                                         let !appl_55 = Atom Nil
                                                                         !appl_56 <- appl_54 `pseq` (appl_55 `pseq` klCons appl_54 appl_55)
                                                                         !appl_57 <- appl_56 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_56
                                                                         let !appl_58 = Atom Nil
                                                                         !appl_59 <- appl_57 `pseq` (appl_58 `pseq` klCons appl_57 appl_58)
                                                                         !appl_60 <- appl_59 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_59
                                                                         let !appl_61 = Atom Nil
                                                                         !appl_62 <- appl_60 `pseq` (appl_61 `pseq` klCons appl_60 appl_61)
                                                                         !appl_63 <- appl_51 `pseq` (appl_62 `pseq` klCons appl_51 appl_62)
                                                                         !appl_64 <- appl_63 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "and")) appl_63
                                                                         appl_64 `pseq` applyWrapper appl_0 [appl_64]

kl_shen_decons :: Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_decons (!kl_V4202) = do !kl_if_0 <- let pat_cond_1 kl_V4202 kl_V4202h kl_V4202t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V4202t kl_V4202th kl_V4202tt = do !kl_if_6 <- let pat_cond_7 kl_V4202tt kl_V4202tth kl_V4202ttt = do let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                !kl_if_9 <- appl_8 `pseq` (kl_V4202tth `pseq` eq appl_8 kl_V4202tth)
                                                                                                                                                                                                                                                                !kl_if_10 <- case kl_if_9 of
                                                                                                                                                                                                                                                                                 Atom (B (True)) -> do let !appl_11 = Atom Nil
                                                                                                                                                                                                                                                                                                       !kl_if_12 <- appl_11 `pseq` (kl_V4202ttt `pseq` eq appl_11 kl_V4202ttt)
                                                                                                                                                                                                                                                                                                       case kl_if_12 of
                                                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                case kl_if_10 of
                                                                                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                                                             pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                          in case kl_V4202tt of
                                                                                                                                                                                                                 !(kl_V4202tt@(Cons (!kl_V4202tth)
                                                                                                                                                                                                                                    (!kl_V4202ttt))) -> pat_cond_7 kl_V4202tt kl_V4202tth kl_V4202ttt
                                                                                                                                                                                                                 _ -> pat_cond_13
                                                                                                                                                                                             case kl_if_6 of
                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                             pat_cond_14 = do do return (Atom (B False))
                                                                                                                                          in case kl_V4202t of
                                                                                                                                                 !(kl_V4202t@(Cons (!kl_V4202th)
                                                                                                                                                                   (!kl_V4202tt))) -> pat_cond_5 kl_V4202t kl_V4202th kl_V4202tt
                                                                                                                                                 _ -> pat_cond_14
                                                                                                                             case kl_if_4 of
                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                             pat_cond_15 = do do return (Atom (B False))
                                                                                                          in case kl_V4202h of
                                                                                                                 kl_V4202h@(Atom (UnboundSym "cons")) -> pat_cond_3
                                                                                                                 kl_V4202h@(ApplC (PL "cons"
                                                                                                                                      _)) -> pat_cond_3
                                                                                                                 kl_V4202h@(ApplC (Func "cons"
                                                                                                                                        _)) -> pat_cond_3
                                                                                                                 _ -> pat_cond_15
                                                                                             case kl_if_2 of
                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                 _ -> throwError "if: expected boolean"
                                                pat_cond_16 = do do return (Atom (B False))
                                             in case kl_V4202 of
                                                    !(kl_V4202@(Cons (!kl_V4202h)
                                                                     (!kl_V4202t))) -> pat_cond_1 kl_V4202 kl_V4202h kl_V4202t
                                                    _ -> pat_cond_16
                                case kl_if_0 of
                                    Atom (B (True)) -> do !appl_17 <- kl_V4202 `pseq` tl kl_V4202
                                                          !appl_18 <- appl_17 `pseq` hd appl_17
                                                          let !appl_19 = Atom Nil
                                                          appl_18 `pseq` (appl_19 `pseq` klCons appl_18 appl_19)
                                    Atom (B (False)) -> do !kl_if_20 <- let pat_cond_21 kl_V4202 kl_V4202h kl_V4202t = do !kl_if_22 <- let pat_cond_23 = do !kl_if_24 <- let pat_cond_25 kl_V4202t kl_V4202th kl_V4202tt = do !kl_if_26 <- let pat_cond_27 kl_V4202tt kl_V4202tth kl_V4202ttt = do let !appl_28 = Atom Nil
                                                                                                                                                                                                                                                                                                   !kl_if_29 <- appl_28 `pseq` (kl_V4202ttt `pseq` eq appl_28 kl_V4202ttt)
                                                                                                                                                                                                                                                                                                   case kl_if_29 of
                                                                                                                                                                                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                               pat_cond_30 = do do return (Atom (B False))
                                                                                                                                                                                                                                            in case kl_V4202tt of
                                                                                                                                                                                                                                                   !(kl_V4202tt@(Cons (!kl_V4202tth)
                                                                                                                                                                                                                                                                      (!kl_V4202ttt))) -> pat_cond_27 kl_V4202tt kl_V4202tth kl_V4202ttt
                                                                                                                                                                                                                                                   _ -> pat_cond_30
                                                                                                                                                                                                                              case kl_if_26 of
                                                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                             pat_cond_31 = do do return (Atom (B False))
                                                                                                                                                                          in case kl_V4202t of
                                                                                                                                                                                 !(kl_V4202t@(Cons (!kl_V4202th)
                                                                                                                                                                                                   (!kl_V4202tt))) -> pat_cond_25 kl_V4202t kl_V4202th kl_V4202tt
                                                                                                                                                                                 _ -> pat_cond_31
                                                                                                                                                            case kl_if_24 of
                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                           pat_cond_32 = do do return (Atom (B False))
                                                                                                                                        in case kl_V4202h of
                                                                                                                                               kl_V4202h@(Atom (UnboundSym "cons")) -> pat_cond_23
                                                                                                                                               kl_V4202h@(ApplC (PL "cons"
                                                                                                                                                                    _)) -> pat_cond_23
                                                                                                                                               kl_V4202h@(ApplC (Func "cons"
                                                                                                                                                                      _)) -> pat_cond_23
                                                                                                                                               _ -> pat_cond_32
                                                                                                                          case kl_if_22 of
                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                              _ -> throwError "if: expected boolean"
                                                                            pat_cond_33 = do do return (Atom (B False))
                                                                         in case kl_V4202 of
                                                                                !(kl_V4202@(Cons (!kl_V4202h)
                                                                                                 (!kl_V4202t))) -> pat_cond_21 kl_V4202 kl_V4202h kl_V4202t
                                                                                _ -> pat_cond_33
                                                           case kl_if_20 of
                                                               Atom (B (True)) -> do !appl_34 <- kl_V4202 `pseq` tl kl_V4202
                                                                                     !appl_35 <- appl_34 `pseq` hd appl_34
                                                                                     !appl_36 <- kl_V4202 `pseq` tl kl_V4202
                                                                                     !appl_37 <- appl_36 `pseq` tl appl_36
                                                                                     !appl_38 <- appl_37 `pseq` hd appl_37
                                                                                     !appl_39 <- appl_38 `pseq` kl_shen_decons appl_38
                                                                                     appl_35 `pseq` (appl_39 `pseq` klCons appl_35 appl_39)
                                                               Atom (B (False)) -> do do return kl_V4202
                                                               _ -> throwError "if: expected boolean"
                                    _ -> throwError "if: expected boolean"

kl_shen_insert_runon :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_insert_runon (!kl_V4217) (!kl_V4218) (!kl_V4219) = do !kl_if_0 <- let pat_cond_1 kl_V4219 kl_V4219h kl_V4219t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V4219t kl_V4219th kl_V4219tt = do !kl_if_6 <- let pat_cond_7 kl_V4219tt kl_V4219tth kl_V4219ttt = do let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                                              !kl_if_9 <- appl_8 `pseq` (kl_V4219ttt `pseq` eq appl_8 kl_V4219ttt)
                                                                                                                                                                                                                                                                                              !kl_if_10 <- case kl_if_9 of
                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do !kl_if_11 <- kl_V4219tth `pseq` (kl_V4218 `pseq` eq kl_V4219tth kl_V4218)
                                                                                                                                                                                                                                                                                                                                     case kl_if_11 of
                                                                                                                                                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                              case kl_if_10 of
                                                                                                                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                           pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                        in case kl_V4219tt of
                                                                                                                                                                                                                                               !(kl_V4219tt@(Cons (!kl_V4219tth)
                                                                                                                                                                                                                                                                  (!kl_V4219ttt))) -> pat_cond_7 kl_V4219tt kl_V4219tth kl_V4219ttt
                                                                                                                                                                                                                                               _ -> pat_cond_12
                                                                                                                                                                                                                           case kl_if_6 of
                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                           pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                        in case kl_V4219t of
                                                                                                                                                                               !(kl_V4219t@(Cons (!kl_V4219th)
                                                                                                                                                                                                 (!kl_V4219tt))) -> pat_cond_5 kl_V4219t kl_V4219th kl_V4219tt
                                                                                                                                                                               _ -> pat_cond_13
                                                                                                                                                           case kl_if_4 of
                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                           pat_cond_14 = do do return (Atom (B False))
                                                                                                                                        in case kl_V4219h of
                                                                                                                                               kl_V4219h@(Atom (UnboundSym "shen.pair")) -> pat_cond_3
                                                                                                                                               kl_V4219h@(ApplC (PL "shen.pair"
                                                                                                                                                                    _)) -> pat_cond_3
                                                                                                                                               kl_V4219h@(ApplC (Func "shen.pair"
                                                                                                                                                                      _)) -> pat_cond_3
                                                                                                                                               _ -> pat_cond_14
                                                                                                                           case kl_if_2 of
                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                               _ -> throwError "if: expected boolean"
                                                                              pat_cond_15 = do do return (Atom (B False))
                                                                           in case kl_V4219 of
                                                                                  !(kl_V4219@(Cons (!kl_V4219h)
                                                                                                   (!kl_V4219t))) -> pat_cond_1 kl_V4219 kl_V4219h kl_V4219t
                                                                                  _ -> pat_cond_15
                                                              case kl_if_0 of
                                                                  Atom (B (True)) -> do return kl_V4217
                                                                  Atom (B (False)) -> do let pat_cond_16 kl_V4219 kl_V4219h kl_V4219t = do let !appl_17 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_V4217 `pseq` (kl_V4218 `pseq` (kl_Z `pseq` kl_shen_insert_runon kl_V4217 kl_V4218 kl_Z)))))
                                                                                                                                           appl_17 `pseq` (kl_V4219 `pseq` kl_map appl_17 kl_V4219)
                                                                                             pat_cond_18 = do do return kl_V4219
                                                                                          in case kl_V4219 of
                                                                                                 !(kl_V4219@(Cons (!kl_V4219h)
                                                                                                                  (!kl_V4219t))) -> pat_cond_16 kl_V4219 kl_V4219h kl_V4219t
                                                                                                 _ -> pat_cond_18
                                                                  _ -> throwError "if: expected boolean"

kl_shen_strip_pathname :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_strip_pathname (!kl_V4225) = do !appl_0 <- kl_V4225 `pseq` kl_elementP (Core.Types.Atom (Core.Types.Str ".")) kl_V4225
                                        !kl_if_1 <- appl_0 `pseq` kl_not appl_0
                                        case kl_if_1 of
                                            Atom (B (True)) -> do return kl_V4225
                                            Atom (B (False)) -> do let pat_cond_2 kl_V4225 kl_V4225h kl_V4225t = do kl_V4225t `pseq` kl_shen_strip_pathname kl_V4225t
                                                                       pat_cond_3 = do do let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                          applyWrapper aw_4 [ApplC (wrapNamed "shen.strip-pathname" kl_shen_strip_pathname)]
                                                                    in case kl_V4225 of
                                                                           !(kl_V4225@(Cons (!kl_V4225h)
                                                                                            (!kl_V4225t))) -> pat_cond_2 kl_V4225 kl_V4225h kl_V4225t
                                                                           _ -> pat_cond_3
                                            _ -> throwError "if: expected boolean"

kl_shen_recursive_descent :: Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_recursive_descent (!kl_V4229) (!kl_V4230) (!kl_V4231) = do let pat_cond_0 kl_V4229 kl_V4229h kl_V4229t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do !appl_4 <- kl_V4229h `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "Parse_")) kl_V4229h
                                                                                                                                                                                                                                                                                                                   let !appl_5 = Atom Nil
                                                                                                                                                                                                                                                                                                                   !appl_6 <- appl_5 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_5
                                                                                                                                                                                                                                                                                                                   !appl_7 <- kl_V4229h `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "Parse_")) kl_V4229h
                                                                                                                                                                                                                                                                                                                   let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                                                                   !appl_9 <- appl_7 `pseq` (appl_8 `pseq` klCons appl_7 appl_8)
                                                                                                                                                                                                                                                                                                                   !appl_10 <- appl_6 `pseq` (appl_9 `pseq` klCons appl_6 appl_9)
                                                                                                                                                                                                                                                                                                                   !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_10
                                                                                                                                                                                                                                                                                                                   let !appl_12 = Atom Nil
                                                                                                                                                                                                                                                                                                                   !appl_13 <- appl_11 `pseq` (appl_12 `pseq` klCons appl_11 appl_12)
                                                                                                                                                                                                                                                                                                                   !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_13
                                                                                                                                                                                                                                                                                                                   let !appl_15 = Atom Nil
                                                                                                                                                                                                                                                                                                                   !appl_16 <- kl_Else `pseq` (appl_15 `pseq` klCons kl_Else appl_15)
                                                                                                                                                                                                                                                                                                                   !appl_17 <- kl_Action `pseq` (appl_16 `pseq` klCons kl_Action appl_16)
                                                                                                                                                                                                                                                                                                                   !appl_18 <- appl_14 `pseq` (appl_17 `pseq` klCons appl_14 appl_17)
                                                                                                                                                                                                                                                                                                                   !appl_19 <- appl_18 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_18
                                                                                                                                                                                                                                                                                                                   let !appl_20 = Atom Nil
                                                                                                                                                                                                                                                                                                                   !appl_21 <- appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)
                                                                                                                                                                                                                                                                                                                   !appl_22 <- kl_Test `pseq` (appl_21 `pseq` klCons kl_Test appl_21)
                                                                                                                                                                                                                                                                                                                   !appl_23 <- appl_4 `pseq` (appl_22 `pseq` klCons appl_4 appl_22)
                                                                                                                                                                                                                                                                                                                   appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_23)))
                                                                                                                                                                                                                                                    let !appl_24 = Atom Nil
                                                                                                                                                                                                                                                    !appl_25 <- appl_24 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_24
                                                                                                                                                                                                                                                    appl_25 `pseq` applyWrapper appl_3 [appl_25])))
                                                                                                                                                                                   !appl_26 <- kl_V4229h `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "Parse_")) kl_V4229h
                                                                                                                                                                                   !appl_27 <- kl_V4229t `pseq` (appl_26 `pseq` (kl_V4231 `pseq` kl_shen_syntax kl_V4229t appl_26 kl_V4231))
                                                                                                                                                                                   appl_27 `pseq` applyWrapper appl_2 [appl_27])))
                                                                                                                    let !appl_28 = Atom Nil
                                                                                                                    !appl_29 <- kl_V4230 `pseq` (appl_28 `pseq` klCons kl_V4230 appl_28)
                                                                                                                    !appl_30 <- kl_V4229h `pseq` (appl_29 `pseq` klCons kl_V4229h appl_29)
                                                                                                                    appl_30 `pseq` applyWrapper appl_1 [appl_30]
                                                                       pat_cond_31 = do do let !aw_32 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                           applyWrapper aw_32 [ApplC (wrapNamed "shen.recursive_descent" kl_shen_recursive_descent)]
                                                                    in case kl_V4229 of
                                                                           !(kl_V4229@(Cons (!kl_V4229h)
                                                                                            (!kl_V4229t))) -> pat_cond_0 kl_V4229 kl_V4229h kl_V4229t
                                                                           _ -> pat_cond_31

kl_shen_variable_match :: Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_variable_match (!kl_V4235) (!kl_V4236) (!kl_V4237) = do let pat_cond_0 kl_V4235 kl_V4235h kl_V4235t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do let !appl_4 = Atom Nil
                                                                                                                                                                                                                                                                                                                !appl_5 <- kl_Else `pseq` (appl_4 `pseq` klCons kl_Else appl_4)
                                                                                                                                                                                                                                                                                                                !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                                                                !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                                                                appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                                                                 let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                 !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_8
                                                                                                                                                                                                                                                 appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                                                                                                                !appl_10 <- kl_V4235h `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "Parse_")) kl_V4235h
                                                                                                                                                                                let !appl_11 = Atom Nil
                                                                                                                                                                                !appl_12 <- kl_V4236 `pseq` (appl_11 `pseq` klCons kl_V4236 appl_11)
                                                                                                                                                                                !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_12
                                                                                                                                                                                let !appl_14 = Atom Nil
                                                                                                                                                                                !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                                                                                                                                                                                !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_15
                                                                                                                                                                                let !appl_17 = Atom Nil
                                                                                                                                                                                !appl_18 <- kl_V4236 `pseq` (appl_17 `pseq` klCons kl_V4236 appl_17)
                                                                                                                                                                                !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_18
                                                                                                                                                                                let !appl_20 = Atom Nil
                                                                                                                                                                                !appl_21 <- appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)
                                                                                                                                                                                !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_21
                                                                                                                                                                                let !appl_23 = Atom Nil
                                                                                                                                                                                !appl_24 <- kl_V4236 `pseq` (appl_23 `pseq` klCons kl_V4236 appl_23)
                                                                                                                                                                                !appl_25 <- appl_24 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_24
                                                                                                                                                                                let !appl_26 = Atom Nil
                                                                                                                                                                                !appl_27 <- appl_25 `pseq` (appl_26 `pseq` klCons appl_25 appl_26)
                                                                                                                                                                                !appl_28 <- appl_22 `pseq` (appl_27 `pseq` klCons appl_22 appl_27)
                                                                                                                                                                                !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_28
                                                                                                                                                                                !appl_30 <- kl_V4235t `pseq` (appl_29 `pseq` (kl_V4237 `pseq` kl_shen_syntax kl_V4235t appl_29 kl_V4237))
                                                                                                                                                                                let !appl_31 = Atom Nil
                                                                                                                                                                                !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                                                                                                                                !appl_33 <- appl_16 `pseq` (appl_32 `pseq` klCons appl_16 appl_32)
                                                                                                                                                                                !appl_34 <- appl_10 `pseq` (appl_33 `pseq` klCons appl_10 appl_33)
                                                                                                                                                                                !appl_35 <- appl_34 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_34
                                                                                                                                                                                appl_35 `pseq` applyWrapper appl_2 [appl_35])))
                                                                                                                 let !appl_36 = Atom Nil
                                                                                                                 !appl_37 <- kl_V4236 `pseq` (appl_36 `pseq` klCons kl_V4236 appl_36)
                                                                                                                 !appl_38 <- appl_37 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_37
                                                                                                                 let !appl_39 = Atom Nil
                                                                                                                 !appl_40 <- appl_38 `pseq` (appl_39 `pseq` klCons appl_38 appl_39)
                                                                                                                 !appl_41 <- appl_40 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_40
                                                                                                                 appl_41 `pseq` applyWrapper appl_1 [appl_41]
                                                                    pat_cond_42 = do do let !aw_43 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                        applyWrapper aw_43 [ApplC (wrapNamed "shen.variable-match" kl_shen_variable_match)]
                                                                 in case kl_V4235 of
                                                                        !(kl_V4235@(Cons (!kl_V4235h)
                                                                                         (!kl_V4235t))) -> pat_cond_0 kl_V4235 kl_V4235h kl_V4235t
                                                                        _ -> pat_cond_42

kl_shen_terminalP :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_terminalP (!kl_V4247) = do let pat_cond_0 kl_V4247 kl_V4247h kl_V4247t = do return (Atom (B False))
                                       pat_cond_1 = do !kl_if_2 <- kl_V4247 `pseq` kl_variableP kl_V4247
                                                       case kl_if_2 of
                                                           Atom (B (True)) -> do return (Atom (B False))
                                                           Atom (B (False)) -> do do return (Atom (B True))
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V4247 of
                                           !(kl_V4247@(Cons (!kl_V4247h)
                                                            (!kl_V4247t))) -> pat_cond_0 kl_V4247 kl_V4247h kl_V4247t
                                           _ -> pat_cond_1

kl_shen_jump_streamP :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_jump_streamP (!kl_V4253) = do let pat_cond_0 = do return (Atom (B True))
                                          pat_cond_1 = do do return (Atom (B False))
                                       in case kl_V4253 of
                                              kl_V4253@(Atom (UnboundSym "_")) -> pat_cond_0
                                              kl_V4253@(ApplC (PL "_" _)) -> pat_cond_0
                                              kl_V4253@(ApplC (Func "_" _)) -> pat_cond_0
                                              _ -> pat_cond_1

kl_shen_check_stream :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_check_stream (!kl_V4257) (!kl_V4258) (!kl_V4259) = do let pat_cond_0 kl_V4257 kl_V4257h kl_V4257t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do let !appl_4 = Atom Nil
                                                                                                                                                                                                                                                                                                              !appl_5 <- kl_Else `pseq` (appl_4 `pseq` klCons kl_Else appl_4)
                                                                                                                                                                                                                                                                                                              !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                                                              !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                                                              appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                                                               let !appl_8 = Atom Nil
                                                                                                                                                                                                                                               !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_8
                                                                                                                                                                                                                                               appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                                                                                                              let !appl_10 = Atom Nil
                                                                                                                                                                              !appl_11 <- kl_V4258 `pseq` (appl_10 `pseq` klCons kl_V4258 appl_10)
                                                                                                                                                                              !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_11
                                                                                                                                                                              let !appl_13 = Atom Nil
                                                                                                                                                                              !appl_14 <- appl_12 `pseq` (appl_13 `pseq` klCons appl_12 appl_13)
                                                                                                                                                                              !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_14
                                                                                                                                                                              let !appl_16 = Atom Nil
                                                                                                                                                                              !appl_17 <- kl_V4258 `pseq` (appl_16 `pseq` klCons kl_V4258 appl_16)
                                                                                                                                                                              !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_17
                                                                                                                                                                              let !appl_19 = Atom Nil
                                                                                                                                                                              !appl_20 <- appl_18 `pseq` (appl_19 `pseq` klCons appl_18 appl_19)
                                                                                                                                                                              !appl_21 <- appl_15 `pseq` (appl_20 `pseq` klCons appl_15 appl_20)
                                                                                                                                                                              !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_21
                                                                                                                                                                              !appl_23 <- kl_V4257t `pseq` (appl_22 `pseq` (kl_V4259 `pseq` kl_shen_syntax kl_V4257t appl_22 kl_V4259))
                                                                                                                                                                              appl_23 `pseq` applyWrapper appl_2 [appl_23])))
                                                                                                               let !appl_24 = Atom Nil
                                                                                                               !appl_25 <- kl_V4258 `pseq` (appl_24 `pseq` klCons kl_V4258 appl_24)
                                                                                                               !appl_26 <- appl_25 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_25
                                                                                                               let !appl_27 = Atom Nil
                                                                                                               !appl_28 <- appl_26 `pseq` (appl_27 `pseq` klCons appl_26 appl_27)
                                                                                                               !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_28
                                                                                                               let !appl_30 = Atom Nil
                                                                                                               !appl_31 <- kl_V4258 `pseq` (appl_30 `pseq` klCons kl_V4258 appl_30)
                                                                                                               !appl_32 <- appl_31 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_31
                                                                                                               let !appl_33 = Atom Nil
                                                                                                               !appl_34 <- appl_32 `pseq` (appl_33 `pseq` klCons appl_32 appl_33)
                                                                                                               !appl_35 <- appl_34 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_34
                                                                                                               let !appl_36 = Atom Nil
                                                                                                               !appl_37 <- appl_35 `pseq` (appl_36 `pseq` klCons appl_35 appl_36)
                                                                                                               !appl_38 <- kl_V4257h `pseq` (appl_37 `pseq` klCons kl_V4257h appl_37)
                                                                                                               !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_38
                                                                                                               let !appl_40 = Atom Nil
                                                                                                               !appl_41 <- appl_39 `pseq` (appl_40 `pseq` klCons appl_39 appl_40)
                                                                                                               !appl_42 <- appl_29 `pseq` (appl_41 `pseq` klCons appl_29 appl_41)
                                                                                                               !appl_43 <- appl_42 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "and")) appl_42
                                                                                                               appl_43 `pseq` applyWrapper appl_1 [appl_43]
                                                                  pat_cond_44 = do do let !aw_45 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                      applyWrapper aw_45 [ApplC (wrapNamed "shen.check_stream" kl_shen_check_stream)]
                                                               in case kl_V4257 of
                                                                      !(kl_V4257@(Cons (!kl_V4257h)
                                                                                       (!kl_V4257t))) -> pat_cond_0 kl_V4257 kl_V4257h kl_V4257t
                                                                      _ -> pat_cond_44

kl_shen_jump_stream :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_jump_stream (!kl_V4263) (!kl_V4264) (!kl_V4265) = do let pat_cond_0 kl_V4263 kl_V4263h kl_V4263t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do let !appl_4 = Atom Nil
                                                                                                                                                                                                                                                                                                             !appl_5 <- kl_Else `pseq` (appl_4 `pseq` klCons kl_Else appl_4)
                                                                                                                                                                                                                                                                                                             !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                                                             !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                                                             appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                                                              let !appl_8 = Atom Nil
                                                                                                                                                                                                                                              !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_8
                                                                                                                                                                                                                                              appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                                                                                                             let !appl_10 = Atom Nil
                                                                                                                                                                             !appl_11 <- kl_V4264 `pseq` (appl_10 `pseq` klCons kl_V4264 appl_10)
                                                                                                                                                                             !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_11
                                                                                                                                                                             let !appl_13 = Atom Nil
                                                                                                                                                                             !appl_14 <- appl_12 `pseq` (appl_13 `pseq` klCons appl_12 appl_13)
                                                                                                                                                                             !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_14
                                                                                                                                                                             let !appl_16 = Atom Nil
                                                                                                                                                                             !appl_17 <- kl_V4264 `pseq` (appl_16 `pseq` klCons kl_V4264 appl_16)
                                                                                                                                                                             !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_17
                                                                                                                                                                             let !appl_19 = Atom Nil
                                                                                                                                                                             !appl_20 <- appl_18 `pseq` (appl_19 `pseq` klCons appl_18 appl_19)
                                                                                                                                                                             !appl_21 <- appl_15 `pseq` (appl_20 `pseq` klCons appl_15 appl_20)
                                                                                                                                                                             !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_21
                                                                                                                                                                             !appl_23 <- kl_V4263t `pseq` (appl_22 `pseq` (kl_V4265 `pseq` kl_shen_syntax kl_V4263t appl_22 kl_V4265))
                                                                                                                                                                             appl_23 `pseq` applyWrapper appl_2 [appl_23])))
                                                                                                              let !appl_24 = Atom Nil
                                                                                                              !appl_25 <- kl_V4264 `pseq` (appl_24 `pseq` klCons kl_V4264 appl_24)
                                                                                                              !appl_26 <- appl_25 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_25
                                                                                                              let !appl_27 = Atom Nil
                                                                                                              !appl_28 <- appl_26 `pseq` (appl_27 `pseq` klCons appl_26 appl_27)
                                                                                                              !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_28
                                                                                                              appl_29 `pseq` applyWrapper appl_1 [appl_29]
                                                                 pat_cond_30 = do do let !aw_31 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                     applyWrapper aw_31 [ApplC (wrapNamed "shen.jump_stream" kl_shen_jump_stream)]
                                                              in case kl_V4263 of
                                                                     !(kl_V4263@(Cons (!kl_V4263h)
                                                                                      (!kl_V4263t))) -> pat_cond_0 kl_V4263 kl_V4263h kl_V4263t
                                                                     _ -> pat_cond_30

kl_shen_semantics :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_semantics (!kl_V4267) = do let !appl_0 = Atom Nil
                                   !kl_if_1 <- appl_0 `pseq` (kl_V4267 `pseq` eq appl_0 kl_V4267)
                                   case kl_if_1 of
                                       Atom (B (True)) -> do return (Atom Nil)
                                       Atom (B (False)) -> do !kl_if_2 <- kl_V4267 `pseq` kl_shen_grammar_symbolP kl_V4267
                                                              case kl_if_2 of
                                                                  Atom (B (True)) -> do !appl_3 <- kl_V4267 `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "Parse_")) kl_V4267
                                                                                        let !appl_4 = Atom Nil
                                                                                        !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                        appl_5 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_5
                                                                  Atom (B (False)) -> do !kl_if_6 <- kl_V4267 `pseq` kl_variableP kl_V4267
                                                                                         case kl_if_6 of
                                                                                             Atom (B (True)) -> do kl_V4267 `pseq` kl_concat (Core.Types.Atom (Core.Types.UnboundSym "Parse_")) kl_V4267
                                                                                             Atom (B (False)) -> do let pat_cond_7 kl_V4267 kl_V4267h kl_V4267t = do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_semantics kl_Z)))
                                                                                                                                                                     appl_8 `pseq` (kl_V4267 `pseq` kl_map appl_8 kl_V4267)
                                                                                                                        pat_cond_9 = do do return kl_V4267
                                                                                                                     in case kl_V4267 of
                                                                                                                            !(kl_V4267@(Cons (!kl_V4267h)
                                                                                                                                             (!kl_V4267t))) -> pat_cond_7 kl_V4267 kl_V4267h kl_V4267t
                                                                                                                            _ -> pat_cond_9
                                                                                             _ -> throwError "if: expected boolean"
                                                                  _ -> throwError "if: expected boolean"
                                       _ -> throwError "if: expected boolean"

kl_shen_snd_or_fail :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_snd_or_fail (!kl_V4275) = do !kl_if_0 <- let pat_cond_1 kl_V4275 kl_V4275h kl_V4275t = do !kl_if_2 <- let pat_cond_3 kl_V4275t kl_V4275th kl_V4275tt = do let !appl_4 = Atom Nil
                                                                                                                                                                  !kl_if_5 <- appl_4 `pseq` (kl_V4275tt `pseq` eq appl_4 kl_V4275tt)
                                                                                                                                                                  case kl_if_5 of
                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                  pat_cond_6 = do do return (Atom (B False))
                                                                                                               in case kl_V4275t of
                                                                                                                      !(kl_V4275t@(Cons (!kl_V4275th)
                                                                                                                                        (!kl_V4275tt))) -> pat_cond_3 kl_V4275t kl_V4275th kl_V4275tt
                                                                                                                      _ -> pat_cond_6
                                                                                                  case kl_if_2 of
                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                      _ -> throwError "if: expected boolean"
                                                     pat_cond_7 = do do return (Atom (B False))
                                                  in case kl_V4275 of
                                                         !(kl_V4275@(Cons (!kl_V4275h)
                                                                          (!kl_V4275t))) -> pat_cond_1 kl_V4275 kl_V4275h kl_V4275t
                                                         _ -> pat_cond_7
                                     case kl_if_0 of
                                         Atom (B (True)) -> do !appl_8 <- kl_V4275 `pseq` tl kl_V4275
                                                               appl_8 `pseq` hd appl_8
                                         Atom (B (False)) -> do do kl_fail
                                         _ -> throwError "if: expected boolean"

kl_fail :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_fail = do return (Core.Types.Atom (Core.Types.UnboundSym "shen.fail!"))

kl_shen_pair :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_pair (!kl_V4278) (!kl_V4279) = do let !appl_0 = Atom Nil
                                          !appl_1 <- kl_V4279 `pseq` (appl_0 `pseq` klCons kl_V4279 appl_0)
                                          kl_V4278 `pseq` (appl_1 `pseq` klCons kl_V4278 appl_1)

kl_shen_hdtl :: Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_hdtl (!kl_V4281) = do !appl_0 <- kl_V4281 `pseq` tl kl_V4281
                              appl_0 `pseq` hd appl_0

kl_LBExclRB :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LBExclRB (!kl_V4289) = do !kl_if_0 <- let pat_cond_1 kl_V4289 kl_V4289h kl_V4289t = do !kl_if_2 <- let pat_cond_3 kl_V4289t kl_V4289th kl_V4289tt = do let !appl_4 = Atom Nil
                                                                                                                                                          !kl_if_5 <- appl_4 `pseq` (kl_V4289tt `pseq` eq appl_4 kl_V4289tt)
                                                                                                                                                          case kl_if_5 of
                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                          pat_cond_6 = do do return (Atom (B False))
                                                                                                       in case kl_V4289t of
                                                                                                              !(kl_V4289t@(Cons (!kl_V4289th)
                                                                                                                                (!kl_V4289tt))) -> pat_cond_3 kl_V4289t kl_V4289th kl_V4289tt
                                                                                                              _ -> pat_cond_6
                                                                                          case kl_if_2 of
                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                              _ -> throwError "if: expected boolean"
                                             pat_cond_7 = do do return (Atom (B False))
                                          in case kl_V4289 of
                                                 !(kl_V4289@(Cons (!kl_V4289h)
                                                                  (!kl_V4289t))) -> pat_cond_1 kl_V4289 kl_V4289h kl_V4289t
                                                 _ -> pat_cond_7
                             case kl_if_0 of
                                 Atom (B (True)) -> do let !appl_8 = Atom Nil
                                                       !appl_9 <- kl_V4289 `pseq` hd kl_V4289
                                                       let !appl_10 = Atom Nil
                                                       !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                       appl_8 `pseq` (appl_11 `pseq` klCons appl_8 appl_11)
                                 Atom (B (False)) -> do do kl_fail
                                 _ -> throwError "if: expected boolean"

kl_LBeRB :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LBeRB (!kl_V4295) = do !kl_if_0 <- let pat_cond_1 kl_V4295 kl_V4295h kl_V4295t = do !kl_if_2 <- let pat_cond_3 kl_V4295t kl_V4295th kl_V4295tt = do let !appl_4 = Atom Nil
                                                                                                                                                       !kl_if_5 <- appl_4 `pseq` (kl_V4295tt `pseq` eq appl_4 kl_V4295tt)
                                                                                                                                                       case kl_if_5 of
                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                       pat_cond_6 = do do return (Atom (B False))
                                                                                                    in case kl_V4295t of
                                                                                                           !(kl_V4295t@(Cons (!kl_V4295th)
                                                                                                                             (!kl_V4295tt))) -> pat_cond_3 kl_V4295t kl_V4295th kl_V4295tt
                                                                                                           _ -> pat_cond_6
                                                                                       case kl_if_2 of
                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                           _ -> throwError "if: expected boolean"
                                          pat_cond_7 = do do return (Atom (B False))
                                       in case kl_V4295 of
                                              !(kl_V4295@(Cons (!kl_V4295h)
                                                               (!kl_V4295t))) -> pat_cond_1 kl_V4295 kl_V4295h kl_V4295t
                                              _ -> pat_cond_7
                          case kl_if_0 of
                              Atom (B (True)) -> do !appl_8 <- kl_V4295 `pseq` hd kl_V4295
                                                    let !appl_9 = Atom Nil
                                                    let !appl_10 = Atom Nil
                                                    !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                    appl_8 `pseq` (appl_11 `pseq` klCons appl_8 appl_11)
                              Atom (B (False)) -> do do let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                        applyWrapper aw_12 [ApplC (wrapNamed "<e>" kl_LBeRB)]
                              _ -> throwError "if: expected boolean"

expr4 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr4 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
