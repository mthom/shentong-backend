{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Sys where

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

kl_thaw :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_thaw (!kl_V2632) = do applyWrapper kl_V2632 []

kl_eval :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_eval (!kl_V2634) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Macroexpand) -> do !kl_if_1 <- kl_Macroexpand `pseq` kl_shen_packagedP kl_Macroexpand
                                                                                               case kl_if_1 of
                                                                                                   Atom (B (True)) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_eval_without_macros kl_Z)))
                                                                                                                         !appl_3 <- kl_Macroexpand `pseq` kl_shen_package_contents kl_Macroexpand
                                                                                                                         appl_2 `pseq` (appl_3 `pseq` kl_map appl_2 appl_3)
                                                                                                   Atom (B (False)) -> do do kl_Macroexpand `pseq` kl_shen_eval_without_macros kl_Macroexpand
                                                                                                   _ -> throwError "if: expected boolean")))
                         let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "macroexpand")
                                                                                     kl_Y `pseq` applyWrapper aw_5 [kl_Y])))
                         !appl_6 <- appl_4 `pseq` (kl_V2634 `pseq` kl_shen_walk appl_4 kl_V2634)
                         appl_6 `pseq` applyWrapper appl_0 [appl_6]

kl_shen_eval_without_macros :: Core.Types.KLValue ->
                               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_eval_without_macros (!kl_V2636) = do !appl_0 <- kl_V2636 `pseq` kl_shen_proc_inputPlus kl_V2636
                                             !appl_1 <- appl_0 `pseq` kl_shen_elim_def appl_0
                                             appl_1 `pseq` evalKL appl_1

kl_shen_proc_inputPlus :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_proc_inputPlus (!kl_V2638) = do !kl_if_0 <- let pat_cond_1 kl_V2638 kl_V2638h kl_V2638t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V2638t kl_V2638th kl_V2638tt = do !kl_if_6 <- let pat_cond_7 kl_V2638tt kl_V2638tth kl_V2638ttt = do let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                        !kl_if_9 <- appl_8 `pseq` (kl_V2638ttt `pseq` eq appl_8 kl_V2638ttt)
                                                                                                                                                                                                                                                                        case kl_if_9 of
                                                                                                                                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                     pat_cond_10 = do do return (Atom (B False))
                                                                                                                                                                                                                  in case kl_V2638tt of
                                                                                                                                                                                                                         !(kl_V2638tt@(Cons (!kl_V2638tth)
                                                                                                                                                                                                                                            (!kl_V2638ttt))) -> pat_cond_7 kl_V2638tt kl_V2638tth kl_V2638ttt
                                                                                                                                                                                                                         _ -> pat_cond_10
                                                                                                                                                                                                     case kl_if_6 of
                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                     pat_cond_11 = do do return (Atom (B False))
                                                                                                                                                  in case kl_V2638t of
                                                                                                                                                         !(kl_V2638t@(Cons (!kl_V2638th)
                                                                                                                                                                           (!kl_V2638tt))) -> pat_cond_5 kl_V2638t kl_V2638th kl_V2638tt
                                                                                                                                                         _ -> pat_cond_11
                                                                                                                                     case kl_if_4 of
                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                     pat_cond_12 = do do return (Atom (B False))
                                                                                                                  in case kl_V2638h of
                                                                                                                         kl_V2638h@(Atom (UnboundSym "input+")) -> pat_cond_3
                                                                                                                         kl_V2638h@(ApplC (PL "input+"
                                                                                                                                              _)) -> pat_cond_3
                                                                                                                         kl_V2638h@(ApplC (Func "input+"
                                                                                                                                                _)) -> pat_cond_3
                                                                                                                         _ -> pat_cond_12
                                                                                                     case kl_if_2 of
                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                         _ -> throwError "if: expected boolean"
                                                        pat_cond_13 = do do return (Atom (B False))
                                                     in case kl_V2638 of
                                                            !(kl_V2638@(Cons (!kl_V2638h)
                                                                             (!kl_V2638t))) -> pat_cond_1 kl_V2638 kl_V2638h kl_V2638t
                                                            _ -> pat_cond_13
                                        case kl_if_0 of
                                            Atom (B (True)) -> do !appl_14 <- kl_V2638 `pseq` tl kl_V2638
                                                                  !appl_15 <- appl_14 `pseq` hd appl_14
                                                                  let !aw_16 = Core.Types.Atom (Core.Types.UnboundSym "shen.rcons_form")
                                                                  !appl_17 <- appl_15 `pseq` applyWrapper aw_16 [appl_15]
                                                                  !appl_18 <- kl_V2638 `pseq` tl kl_V2638
                                                                  !appl_19 <- appl_18 `pseq` tl appl_18
                                                                  !appl_20 <- appl_17 `pseq` (appl_19 `pseq` klCons appl_17 appl_19)
                                                                  appl_20 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "input+")) appl_20
                                            Atom (B (False)) -> do !kl_if_21 <- let pat_cond_22 kl_V2638 kl_V2638h kl_V2638t = do !kl_if_23 <- let pat_cond_24 = do !kl_if_25 <- let pat_cond_26 kl_V2638t kl_V2638th kl_V2638tt = do !kl_if_27 <- let pat_cond_28 kl_V2638tt kl_V2638tth kl_V2638ttt = do let !appl_29 = Atom Nil
                                                                                                                                                                                                                                                                                                           !kl_if_30 <- appl_29 `pseq` (kl_V2638ttt `pseq` eq appl_29 kl_V2638ttt)
                                                                                                                                                                                                                                                                                                           case kl_if_30 of
                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                       pat_cond_31 = do do return (Atom (B False))
                                                                                                                                                                                                                                                    in case kl_V2638tt of
                                                                                                                                                                                                                                                           !(kl_V2638tt@(Cons (!kl_V2638tth)
                                                                                                                                                                                                                                                                              (!kl_V2638ttt))) -> pat_cond_28 kl_V2638tt kl_V2638tth kl_V2638ttt
                                                                                                                                                                                                                                                           _ -> pat_cond_31
                                                                                                                                                                                                                                      case kl_if_27 of
                                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                     pat_cond_32 = do do return (Atom (B False))
                                                                                                                                                                                  in case kl_V2638t of
                                                                                                                                                                                         !(kl_V2638t@(Cons (!kl_V2638th)
                                                                                                                                                                                                           (!kl_V2638tt))) -> pat_cond_26 kl_V2638t kl_V2638th kl_V2638tt
                                                                                                                                                                                         _ -> pat_cond_32
                                                                                                                                                                    case kl_if_25 of
                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                   pat_cond_33 = do do return (Atom (B False))
                                                                                                                                                in case kl_V2638h of
                                                                                                                                                       kl_V2638h@(Atom (UnboundSym "shen.read+")) -> pat_cond_24
                                                                                                                                                       kl_V2638h@(ApplC (PL "shen.read+"
                                                                                                                                                                            _)) -> pat_cond_24
                                                                                                                                                       kl_V2638h@(ApplC (Func "shen.read+"
                                                                                                                                                                              _)) -> pat_cond_24
                                                                                                                                                       _ -> pat_cond_33
                                                                                                                                  case kl_if_23 of
                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                    pat_cond_34 = do do return (Atom (B False))
                                                                                 in case kl_V2638 of
                                                                                        !(kl_V2638@(Cons (!kl_V2638h)
                                                                                                         (!kl_V2638t))) -> pat_cond_22 kl_V2638 kl_V2638h kl_V2638t
                                                                                        _ -> pat_cond_34
                                                                   case kl_if_21 of
                                                                       Atom (B (True)) -> do !appl_35 <- kl_V2638 `pseq` tl kl_V2638
                                                                                             !appl_36 <- appl_35 `pseq` hd appl_35
                                                                                             let !aw_37 = Core.Types.Atom (Core.Types.UnboundSym "shen.rcons_form")
                                                                                             !appl_38 <- appl_36 `pseq` applyWrapper aw_37 [appl_36]
                                                                                             !appl_39 <- kl_V2638 `pseq` tl kl_V2638
                                                                                             !appl_40 <- appl_39 `pseq` tl appl_39
                                                                                             !appl_41 <- appl_38 `pseq` (appl_40 `pseq` klCons appl_38 appl_40)
                                                                                             appl_41 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.read+")) appl_41
                                                                       Atom (B (False)) -> do let pat_cond_42 kl_V2638 kl_V2638h kl_V2638t = do let !appl_43 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_proc_inputPlus kl_Z)))
                                                                                                                                                appl_43 `pseq` (kl_V2638 `pseq` kl_map appl_43 kl_V2638)
                                                                                                  pat_cond_44 = do do return kl_V2638
                                                                                               in case kl_V2638 of
                                                                                                      !(kl_V2638@(Cons (!kl_V2638h)
                                                                                                                       (!kl_V2638t))) -> pat_cond_42 kl_V2638 kl_V2638h kl_V2638t
                                                                                                      _ -> pat_cond_44
                                                                       _ -> throwError "if: expected boolean"
                                            _ -> throwError "if: expected boolean"

kl_shen_elim_def :: Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_elim_def (!kl_V2640) = do let pat_cond_0 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt = do kl_V2640th `pseq` (kl_V2640tt `pseq` kl_shen_RBkl kl_V2640th kl_V2640tt)
                                      pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt = do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Default) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Def) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_MacroAdd) -> do return kl_Def)))
                                                                                                                                                                                                                               !appl_5 <- kl_V2640th `pseq` kl_shen_add_macro kl_V2640th
                                                                                                                                                                                                                               appl_5 `pseq` applyWrapper appl_4 [appl_5])))
                                                                                                                                                                 !appl_6 <- kl_V2640tt `pseq` (kl_Default `pseq` kl_append kl_V2640tt kl_Default)
                                                                                                                                                                 !appl_7 <- kl_V2640th `pseq` (appl_6 `pseq` klCons kl_V2640th appl_6)
                                                                                                                                                                 !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "define")) appl_7
                                                                                                                                                                 !appl_9 <- appl_8 `pseq` kl_shen_elim_def appl_8
                                                                                                                                                                 appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                               let !appl_10 = Atom Nil
                                                                                               !appl_11 <- appl_10 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_10
                                                                                               !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "->")) appl_11
                                                                                               !appl_13 <- appl_12 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_12
                                                                                               appl_13 `pseq` applyWrapper appl_2 [appl_13]
                                      pat_cond_14 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt = do let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "shen.yacc")
                                                                                                !appl_16 <- kl_V2640 `pseq` applyWrapper aw_15 [kl_V2640]
                                                                                                appl_16 `pseq` kl_shen_elim_def appl_16
                                      pat_cond_17 kl_V2640 kl_V2640h kl_V2640t = do let !appl_18 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_elim_def kl_Z)))
                                                                                    appl_18 `pseq` (kl_V2640 `pseq` kl_map appl_18 kl_V2640)
                                      pat_cond_19 = do do return kl_V2640
                                   in case kl_V2640 of
                                          !(kl_V2640@(Cons (Atom (UnboundSym "define"))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (ApplC (PL "define" _))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (ApplC (Func "define" _))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (Atom (UnboundSym "defmacro"))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (ApplC (PL "defmacro" _))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (ApplC (Func "defmacro" _))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (Atom (UnboundSym "defcc"))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_14 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (ApplC (PL "defcc" _))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_14 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (ApplC (Func "defcc" _))
                                                           (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                              (!kl_V2640tt)))))) -> pat_cond_14 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt
                                          !(kl_V2640@(Cons (!kl_V2640h)
                                                           (!kl_V2640t))) -> pat_cond_17 kl_V2640 kl_V2640h kl_V2640t
                                          _ -> pat_cond_19

kl_shen_add_macro :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_add_macro (!kl_V2642) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_MacroReg) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_NewMacroReg) -> do !kl_if_2 <- kl_MacroReg `pseq` (kl_NewMacroReg `pseq` eq kl_MacroReg kl_NewMacroReg)
                                                                                                                                                                            case kl_if_2 of
                                                                                                                                                                                Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.UnboundSym "shen.skip"))
                                                                                                                                                                                Atom (B (False)) -> do do !appl_3 <- kl_V2642 `pseq` kl_function kl_V2642
                                                                                                                                                                                                          !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*macros*"))
                                                                                                                                                                                                          !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                                                                                                                          appl_5 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "*macros*")) appl_5
                                                                                                                                                                                _ -> throwError "if: expected boolean")))
                                                                                                      !appl_6 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*macroreg*"))
                                                                                                      let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "adjoin")
                                                                                                      !appl_8 <- kl_V2642 `pseq` (appl_6 `pseq` applyWrapper aw_7 [kl_V2642,
                                                                                                                                                                   appl_6])
                                                                                                      !appl_9 <- appl_8 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*macroreg*")) appl_8
                                                                                                      appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                                   !appl_10 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*macroreg*"))
                                   appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_packagedP :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_packagedP (!kl_V2650) = do let pat_cond_0 kl_V2650 kl_V2650t kl_V2650th kl_V2650tt kl_V2650tth kl_V2650ttt = do return (Atom (B True))
                                       pat_cond_1 = do do return (Atom (B False))
                                    in case kl_V2650 of
                                           !(kl_V2650@(Cons (Atom (UnboundSym "package"))
                                                            (!(kl_V2650t@(Cons (!kl_V2650th)
                                                                               (!(kl_V2650tt@(Cons (!kl_V2650tth)
                                                                                                   (!kl_V2650ttt))))))))) -> pat_cond_0 kl_V2650 kl_V2650t kl_V2650th kl_V2650tt kl_V2650tth kl_V2650ttt
                                           !(kl_V2650@(Cons (ApplC (PL "package" _))
                                                            (!(kl_V2650t@(Cons (!kl_V2650th)
                                                                               (!(kl_V2650tt@(Cons (!kl_V2650tth)
                                                                                                   (!kl_V2650ttt))))))))) -> pat_cond_0 kl_V2650 kl_V2650t kl_V2650th kl_V2650tt kl_V2650tth kl_V2650ttt
                                           !(kl_V2650@(Cons (ApplC (Func "package" _))
                                                            (!(kl_V2650t@(Cons (!kl_V2650th)
                                                                               (!(kl_V2650tt@(Cons (!kl_V2650tth)
                                                                                                   (!kl_V2650ttt))))))))) -> pat_cond_0 kl_V2650 kl_V2650t kl_V2650th kl_V2650tt kl_V2650tth kl_V2650ttt
                                           _ -> pat_cond_1

kl_external :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_external (!kl_V2652) = do let !appl_0 = ApplC (PL "thunk" (do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                 !appl_2 <- kl_V2652 `pseq` applyWrapper aw_1 [kl_V2652,
                                                                                                               Core.Types.Atom (Core.Types.Str " has not been used.\n"),
                                                                                                               Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                 !appl_3 <- appl_2 `pseq` cn (Core.Types.Atom (Core.Types.Str "package ")) appl_2
                                                                 appl_3 `pseq` simpleError appl_3))
                             !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                             kl_V2652 `pseq` (appl_0 `pseq` (appl_4 `pseq` kl_getDivor kl_V2652 (Core.Types.Atom (Core.Types.UnboundSym "shen.external-symbols")) appl_0 appl_4))

kl_internal :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_internal (!kl_V2654) = do let !appl_0 = ApplC (PL "thunk" (do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                 !appl_2 <- kl_V2654 `pseq` applyWrapper aw_1 [kl_V2654,
                                                                                                               Core.Types.Atom (Core.Types.Str " has not been used.\n"),
                                                                                                               Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                 !appl_3 <- appl_2 `pseq` cn (Core.Types.Atom (Core.Types.Str "package ")) appl_2
                                                                 appl_3 `pseq` simpleError appl_3))
                             !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                             kl_V2654 `pseq` (appl_0 `pseq` (appl_4 `pseq` kl_getDivor kl_V2654 (Core.Types.Atom (Core.Types.UnboundSym "shen.internal-symbols")) appl_0 appl_4))

kl_shen_package_contents :: Core.Types.KLValue ->
                            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_package_contents (!kl_V2658) = do let pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt = do return kl_V2658ttt
                                              pat_cond_1 kl_V2658 kl_V2658t kl_V2658th kl_V2658tt kl_V2658tth kl_V2658ttt = do let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.packageh")
                                                                                                                               kl_V2658th `pseq` (kl_V2658tth `pseq` (kl_V2658ttt `pseq` applyWrapper aw_2 [kl_V2658th,
                                                                                                                                                                                                            kl_V2658tth,
                                                                                                                                                                                                            kl_V2658ttt]))
                                              pat_cond_3 = do do let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                 applyWrapper aw_4 [ApplC (wrapNamed "shen.package-contents" kl_shen_package_contents)]
                                           in case kl_V2658 of
                                                  !(kl_V2658@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2658t@(Cons (Atom (UnboundSym "null"))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2658t@(Cons (ApplC (PL "null"
                                                                                                 _))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2658t@(Cons (ApplC (Func "null"
                                                                                                   _))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2658t@(Cons (Atom (UnboundSym "null"))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2658t@(Cons (ApplC (PL "null"
                                                                                                 _))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2658t@(Cons (ApplC (Func "null"
                                                                                                   _))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2658t@(Cons (Atom (UnboundSym "null"))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2658t@(Cons (ApplC (PL "null"
                                                                                                 _))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2658t@(Cons (ApplC (Func "null"
                                                                                                   _))
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_0 kl_V2658 kl_V2658t kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2658t@(Cons (!kl_V2658th)
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_1 kl_V2658 kl_V2658t kl_V2658th kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2658t@(Cons (!kl_V2658th)
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_1 kl_V2658 kl_V2658t kl_V2658th kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  !(kl_V2658@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2658t@(Cons (!kl_V2658th)
                                                                                      (!(kl_V2658tt@(Cons (!kl_V2658tth)
                                                                                                          (!kl_V2658ttt))))))))) -> pat_cond_1 kl_V2658 kl_V2658t kl_V2658th kl_V2658tt kl_V2658tth kl_V2658ttt
                                                  _ -> pat_cond_3

kl_shen_walk :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_walk (!kl_V2661) (!kl_V2662) = do let pat_cond_0 kl_V2662 kl_V2662h kl_V2662t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_V2661 `pseq` (kl_Z `pseq` kl_shen_walk kl_V2661 kl_Z))))
                                                                                           !appl_2 <- appl_1 `pseq` (kl_V2662 `pseq` kl_map appl_1 kl_V2662)
                                                                                           appl_2 `pseq` applyWrapper kl_V2661 [appl_2]
                                              pat_cond_3 = do do kl_V2662 `pseq` applyWrapper kl_V2661 [kl_V2662]
                                           in case kl_V2662 of
                                                  !(kl_V2662@(Cons (!kl_V2662h)
                                                                   (!kl_V2662t))) -> pat_cond_0 kl_V2662 kl_V2662h kl_V2662t
                                                  _ -> pat_cond_3

kl_compile :: Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_compile (!kl_V2666) (!kl_V2667) (!kl_V2668) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_O) -> do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "fail")
                                                                                                                !appl_2 <- applyWrapper aw_1 []
                                                                                                                !kl_if_3 <- appl_2 `pseq` (kl_O `pseq` eq appl_2 kl_O)
                                                                                                                !kl_if_4 <- case kl_if_3 of
                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                Atom (B (False)) -> do do !appl_5 <- kl_O `pseq` hd kl_O
                                                                                                                                                          !appl_6 <- appl_5 `pseq` kl_emptyP appl_5
                                                                                                                                                          !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                                                                                                                                          case kl_if_7 of
                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                case kl_if_4 of
                                                                                                                    Atom (B (True)) -> do kl_O `pseq` applyWrapper kl_V2668 [kl_O]
                                                                                                                    Atom (B (False)) -> do do let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.hdtl")
                                                                                                                                              kl_O `pseq` applyWrapper aw_8 [kl_O]
                                                                                                                    _ -> throwError "if: expected boolean")))
                                                    let !appl_9 = Atom Nil
                                                    let !appl_10 = Atom Nil
                                                    !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                    !appl_12 <- kl_V2667 `pseq` (appl_11 `pseq` klCons kl_V2667 appl_11)
                                                    !appl_13 <- appl_12 `pseq` applyWrapper kl_V2666 [appl_12]
                                                    appl_13 `pseq` applyWrapper appl_0 [appl_13]

kl_fail_if :: Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_fail_if (!kl_V2671) (!kl_V2672) = do !kl_if_0 <- kl_V2672 `pseq` applyWrapper kl_V2671 [kl_V2672]
                                        case kl_if_0 of
                                            Atom (B (True)) -> do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "fail")
                                                                  applyWrapper aw_1 []
                                            Atom (B (False)) -> do do return kl_V2672
                                            _ -> throwError "if: expected boolean"

kl_Ats :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_Ats (!kl_V2675) (!kl_V2676) = do kl_V2675 `pseq` (kl_V2676 `pseq` cn kl_V2675 kl_V2676)

kl_tcP :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_tcP = do value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*"))

kl_ps :: Core.Types.KLValue ->
         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_ps (!kl_V2678) = do let !appl_0 = ApplC (PL "thunk" (do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                           !appl_2 <- kl_V2678 `pseq` applyWrapper aw_1 [kl_V2678,
                                                                                                         Core.Types.Atom (Core.Types.Str " not found.\n"),
                                                                                                         Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                           appl_2 `pseq` simpleError appl_2))
                       !appl_3 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                       kl_V2678 `pseq` (appl_0 `pseq` (appl_3 `pseq` kl_getDivor kl_V2678 (Core.Types.Atom (Core.Types.UnboundSym "shen.source")) appl_0 appl_3))

kl_stinput :: Core.Types.KLContext Core.Types.Env
                                   Core.Types.KLValue
kl_stinput = do value (Core.Types.Atom (Core.Types.UnboundSym "*stinput*"))

kl_LB_addressDivor :: Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LB_addressDivor (!kl_V2682) (!kl_V2683) (!kl_V2684) = do (do kl_V2682 `pseq` (kl_V2683 `pseq` addressFrom kl_V2682 kl_V2683)) `catchError` (\(!kl_E) -> do kl_V2684 `pseq` kl_thaw kl_V2684)

kl_valueDivor :: Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_valueDivor (!kl_V2687) (!kl_V2688) = do (do kl_V2687 `pseq` value kl_V2687) `catchError` (\(!kl_E) -> do kl_V2688 `pseq` kl_thaw kl_V2688)

kl_vector :: Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_vector (!kl_V2690) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Vector) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_ZeroStamp) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Standard) -> do return kl_Standard)))
                                                                                                                                                                !appl_3 <- let pat_cond_4 = do return kl_ZeroStamp
                                                                                                                                                                               pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "fail")
                                                                                                                                                                                                  !appl_7 <- applyWrapper aw_6 []
                                                                                                                                                                                                  kl_ZeroStamp `pseq` (kl_V2690 `pseq` (appl_7 `pseq` kl_shen_fillvector kl_ZeroStamp (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V2690 appl_7))
                                                                                                                                                                            in case kl_V2690 of
                                                                                                                                                                                   kl_V2690@(Atom (N (KI 0))) -> pat_cond_4
                                                                                                                                                                                   _ -> pat_cond_5
                                                                                                                                                                appl_3 `pseq` applyWrapper appl_2 [appl_3])))
                                                                                            !appl_8 <- kl_Vector `pseq` (kl_V2690 `pseq` addressTo kl_Vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) kl_V2690)
                                                                                            appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                           !appl_9 <- kl_V2690 `pseq` add kl_V2690 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                           !appl_10 <- appl_9 `pseq` absvector appl_9
                           appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_fillvector :: Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_fillvector (!kl_V2696) (!kl_V2697) (!kl_V2698) (!kl_V2699) = do !kl_if_0 <- kl_V2698 `pseq` (kl_V2697 `pseq` eq kl_V2698 kl_V2697)
                                                                        case kl_if_0 of
                                                                            Atom (B (True)) -> do kl_V2696 `pseq` (kl_V2698 `pseq` (kl_V2699 `pseq` addressTo kl_V2696 kl_V2698 kl_V2699))
                                                                            Atom (B (False)) -> do do !appl_1 <- kl_V2696 `pseq` (kl_V2697 `pseq` (kl_V2699 `pseq` addressTo kl_V2696 kl_V2697 kl_V2699))
                                                                                                      !appl_2 <- kl_V2697 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V2697
                                                                                                      appl_1 `pseq` (appl_2 `pseq` (kl_V2698 `pseq` (kl_V2699 `pseq` kl_shen_fillvector appl_1 appl_2 kl_V2698 kl_V2699)))
                                                                            _ -> throwError "if: expected boolean"

kl_vectorP :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_vectorP (!kl_V2701) = do !kl_if_0 <- kl_V2701 `pseq` absvectorP kl_V2701
                            case kl_if_0 of
                                Atom (B (True)) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !kl_if_2 <- kl_X `pseq` numberP kl_X
                                                                                                                  case kl_if_2 of
                                                                                                                      Atom (B (True)) -> do !kl_if_3 <- kl_X `pseq` greaterThanOrEqualTo kl_X (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                            case kl_if_3 of
                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                      _ -> throwError "if: expected boolean")))
                                                      let !appl_4 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.N (Core.Types.KI (-1))))))
                                                      !appl_5 <- kl_V2701 `pseq` (appl_4 `pseq` kl_LB_addressDivor kl_V2701 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_4)
                                                      !kl_if_6 <- appl_5 `pseq` applyWrapper appl_1 [appl_5]
                                                      case kl_if_6 of
                                                          Atom (B (True)) -> do return (Atom (B True))
                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                          _ -> throwError "if: expected boolean"
                                Atom (B (False)) -> do do return (Atom (B False))
                                _ -> throwError "if: expected boolean"

kl_vector_RB :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_vector_RB (!kl_V2705) (!kl_V2706) (!kl_V2707) = do let pat_cond_0 = do simpleError (Core.Types.Atom (Core.Types.Str "cannot access 0th element of a vector\n"))
                                                          pat_cond_1 = do do kl_V2705 `pseq` (kl_V2706 `pseq` (kl_V2707 `pseq` addressTo kl_V2705 kl_V2706 kl_V2707))
                                                       in case kl_V2706 of
                                                              kl_V2706@(Atom (N (KI 0))) -> pat_cond_0
                                                              _ -> pat_cond_1

kl_LB_vector :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LB_vector (!kl_V2710) (!kl_V2711) = do let pat_cond_0 = do simpleError (Core.Types.Atom (Core.Types.Str "cannot access 0th element of a vector\n"))
                                              pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_VectorElement) -> do let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "fail")
                                                                                                                                         !appl_4 <- applyWrapper aw_3 []
                                                                                                                                         !kl_if_5 <- kl_VectorElement `pseq` (appl_4 `pseq` eq kl_VectorElement appl_4)
                                                                                                                                         case kl_if_5 of
                                                                                                                                             Atom (B (True)) -> do simpleError (Core.Types.Atom (Core.Types.Str "vector element not found\n"))
                                                                                                                                             Atom (B (False)) -> do do return kl_VectorElement
                                                                                                                                             _ -> throwError "if: expected boolean")))
                                                                 !appl_6 <- kl_V2710 `pseq` (kl_V2711 `pseq` addressFrom kl_V2710 kl_V2711)
                                                                 appl_6 `pseq` applyWrapper appl_2 [appl_6]
                                           in case kl_V2711 of
                                                  kl_V2711@(Atom (N (KI 0))) -> pat_cond_0
                                                  _ -> pat_cond_1

kl_LB_vectorDivor :: Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LB_vectorDivor (!kl_V2715) (!kl_V2716) (!kl_V2717) = do let pat_cond_0 = do simpleError (Core.Types.Atom (Core.Types.Str "cannot access 0th element of a vector\n"))
                                                               pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_VectorElement) -> do let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "fail")
                                                                                                                                                          !appl_4 <- applyWrapper aw_3 []
                                                                                                                                                          !kl_if_5 <- kl_VectorElement `pseq` (appl_4 `pseq` eq kl_VectorElement appl_4)
                                                                                                                                                          case kl_if_5 of
                                                                                                                                                              Atom (B (True)) -> do kl_V2717 `pseq` kl_thaw kl_V2717
                                                                                                                                                              Atom (B (False)) -> do do return kl_VectorElement
                                                                                                                                                              _ -> throwError "if: expected boolean")))
                                                                                  !appl_6 <- kl_V2715 `pseq` (kl_V2716 `pseq` (kl_V2717 `pseq` kl_LB_addressDivor kl_V2715 kl_V2716 kl_V2717))
                                                                                  appl_6 `pseq` applyWrapper appl_2 [appl_6]
                                                            in case kl_V2716 of
                                                                   kl_V2716@(Atom (N (KI 0))) -> pat_cond_0
                                                                   _ -> pat_cond_1

kl_shen_posintP :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_posintP (!kl_V2719) = do !kl_if_0 <- kl_V2719 `pseq` kl_integerP kl_V2719
                                 case kl_if_0 of
                                     Atom (B (True)) -> do !kl_if_1 <- kl_V2719 `pseq` greaterThanOrEqualTo kl_V2719 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                           case kl_if_1 of
                                                               Atom (B (True)) -> do return (Atom (B True))
                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                               _ -> throwError "if: expected boolean"
                                     Atom (B (False)) -> do do return (Atom (B False))
                                     _ -> throwError "if: expected boolean"

kl_limit :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_limit (!kl_V2721) = do kl_V2721 `pseq` addressFrom kl_V2721 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))

kl_symbolP :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_symbolP (!kl_V2723) = do !kl_if_0 <- kl_V2723 `pseq` kl_booleanP kl_V2723
                            !kl_if_1 <- case kl_if_0 of
                                            Atom (B (True)) -> do return (Atom (B True))
                                            Atom (B (False)) -> do do !kl_if_2 <- kl_V2723 `pseq` numberP kl_V2723
                                                                      !kl_if_3 <- case kl_if_2 of
                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                      Atom (B (False)) -> do do !kl_if_4 <- kl_V2723 `pseq` stringP kl_V2723
                                                                                                                case kl_if_4 of
                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                      _ -> throwError "if: expected boolean"
                                                                      case kl_if_3 of
                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                          _ -> throwError "if: expected boolean"
                                            _ -> throwError "if: expected boolean"
                            case kl_if_1 of
                                Atom (B (True)) -> do return (Atom (B False))
                                Atom (B (False)) -> do do (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_String) -> do kl_String `pseq` kl_shen_analyse_symbolP kl_String)))
                                                              !appl_6 <- kl_V2723 `pseq` str kl_V2723
                                                              appl_6 `pseq` applyWrapper appl_5 [appl_6]) `catchError` (\(!kl_E) -> do return (Atom (B False)))
                                _ -> throwError "if: expected boolean"

kl_shen_analyse_symbolP :: Core.Types.KLValue ->
                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_analyse_symbolP (!kl_V2725) = do let pat_cond_0 = do return (Atom (B False))
                                             pat_cond_1 = do !kl_if_2 <- kl_V2725 `pseq` kl_shen_PlusstringP kl_V2725
                                                             case kl_if_2 of
                                                                 Atom (B (True)) -> do !appl_3 <- kl_V2725 `pseq` pos kl_V2725 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                       !kl_if_4 <- appl_3 `pseq` kl_shen_alphaP appl_3
                                                                                       case kl_if_4 of
                                                                                           Atom (B (True)) -> do !appl_5 <- kl_V2725 `pseq` tlstr kl_V2725
                                                                                                                 !kl_if_6 <- appl_5 `pseq` kl_shen_alphanumsP appl_5
                                                                                                                 case kl_if_6 of
                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                           _ -> throwError "if: expected boolean"
                                                                 Atom (B (False)) -> do do let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                           applyWrapper aw_7 [ApplC (wrapNamed "shen.analyse-symbol?" kl_shen_analyse_symbolP)]
                                                                 _ -> throwError "if: expected boolean"
                                          in case kl_V2725 of
                                                 kl_V2725@(Atom (Str "")) -> pat_cond_0
                                                 _ -> pat_cond_1

kl_shen_alphaP :: Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_alphaP (!kl_V2727) = do let !appl_0 = Atom Nil
                                !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.Str ".")) appl_0
                                !appl_2 <- appl_1 `pseq` klCons (Core.Types.Atom (Core.Types.Str "'")) appl_1
                                !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.Str "#")) appl_2
                                !appl_4 <- appl_3 `pseq` klCons (Core.Types.Atom (Core.Types.Str "`")) appl_3
                                !appl_5 <- appl_4 `pseq` klCons (Core.Types.Atom (Core.Types.Str ";")) appl_4
                                !appl_6 <- appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.Str ":")) appl_5
                                !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.Str "}")) appl_6
                                !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.Str "{")) appl_7
                                !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.Str "%")) appl_8
                                !appl_10 <- appl_9 `pseq` klCons (Core.Types.Atom (Core.Types.Str "&")) appl_9
                                !appl_11 <- appl_10 `pseq` klCons (Core.Types.Atom (Core.Types.Str "<")) appl_10
                                !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.Str ">")) appl_11
                                !appl_13 <- appl_12 `pseq` klCons (Core.Types.Atom (Core.Types.Str "~")) appl_12
                                !appl_14 <- appl_13 `pseq` klCons (Core.Types.Atom (Core.Types.Str "@")) appl_13
                                !appl_15 <- appl_14 `pseq` klCons (Core.Types.Atom (Core.Types.Str "!")) appl_14
                                !appl_16 <- appl_15 `pseq` klCons (Core.Types.Atom (Core.Types.Str "$")) appl_15
                                !appl_17 <- appl_16 `pseq` klCons (Core.Types.Atom (Core.Types.Str "?")) appl_16
                                !appl_18 <- appl_17 `pseq` klCons (Core.Types.Atom (Core.Types.Str "_")) appl_17
                                !appl_19 <- appl_18 `pseq` klCons (Core.Types.Atom (Core.Types.Str "-")) appl_18
                                !appl_20 <- appl_19 `pseq` klCons (Core.Types.Atom (Core.Types.Str "+")) appl_19
                                !appl_21 <- appl_20 `pseq` klCons (Core.Types.Atom (Core.Types.Str "/")) appl_20
                                !appl_22 <- appl_21 `pseq` klCons (Core.Types.Atom (Core.Types.Str "*")) appl_21
                                !appl_23 <- appl_22 `pseq` klCons (Core.Types.Atom (Core.Types.Str "=")) appl_22
                                !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.Str "z")) appl_23
                                !appl_25 <- appl_24 `pseq` klCons (Core.Types.Atom (Core.Types.Str "y")) appl_24
                                !appl_26 <- appl_25 `pseq` klCons (Core.Types.Atom (Core.Types.Str "x")) appl_25
                                !appl_27 <- appl_26 `pseq` klCons (Core.Types.Atom (Core.Types.Str "w")) appl_26
                                !appl_28 <- appl_27 `pseq` klCons (Core.Types.Atom (Core.Types.Str "v")) appl_27
                                !appl_29 <- appl_28 `pseq` klCons (Core.Types.Atom (Core.Types.Str "u")) appl_28
                                !appl_30 <- appl_29 `pseq` klCons (Core.Types.Atom (Core.Types.Str "t")) appl_29
                                !appl_31 <- appl_30 `pseq` klCons (Core.Types.Atom (Core.Types.Str "s")) appl_30
                                !appl_32 <- appl_31 `pseq` klCons (Core.Types.Atom (Core.Types.Str "r")) appl_31
                                !appl_33 <- appl_32 `pseq` klCons (Core.Types.Atom (Core.Types.Str "q")) appl_32
                                !appl_34 <- appl_33 `pseq` klCons (Core.Types.Atom (Core.Types.Str "p")) appl_33
                                !appl_35 <- appl_34 `pseq` klCons (Core.Types.Atom (Core.Types.Str "o")) appl_34
                                !appl_36 <- appl_35 `pseq` klCons (Core.Types.Atom (Core.Types.Str "n")) appl_35
                                !appl_37 <- appl_36 `pseq` klCons (Core.Types.Atom (Core.Types.Str "m")) appl_36
                                !appl_38 <- appl_37 `pseq` klCons (Core.Types.Atom (Core.Types.Str "l")) appl_37
                                !appl_39 <- appl_38 `pseq` klCons (Core.Types.Atom (Core.Types.Str "k")) appl_38
                                !appl_40 <- appl_39 `pseq` klCons (Core.Types.Atom (Core.Types.Str "j")) appl_39
                                !appl_41 <- appl_40 `pseq` klCons (Core.Types.Atom (Core.Types.Str "i")) appl_40
                                !appl_42 <- appl_41 `pseq` klCons (Core.Types.Atom (Core.Types.Str "h")) appl_41
                                !appl_43 <- appl_42 `pseq` klCons (Core.Types.Atom (Core.Types.Str "g")) appl_42
                                !appl_44 <- appl_43 `pseq` klCons (Core.Types.Atom (Core.Types.Str "f")) appl_43
                                !appl_45 <- appl_44 `pseq` klCons (Core.Types.Atom (Core.Types.Str "e")) appl_44
                                !appl_46 <- appl_45 `pseq` klCons (Core.Types.Atom (Core.Types.Str "d")) appl_45
                                !appl_47 <- appl_46 `pseq` klCons (Core.Types.Atom (Core.Types.Str "c")) appl_46
                                !appl_48 <- appl_47 `pseq` klCons (Core.Types.Atom (Core.Types.Str "b")) appl_47
                                !appl_49 <- appl_48 `pseq` klCons (Core.Types.Atom (Core.Types.Str "a")) appl_48
                                !appl_50 <- appl_49 `pseq` klCons (Core.Types.Atom (Core.Types.Str "Z")) appl_49
                                !appl_51 <- appl_50 `pseq` klCons (Core.Types.Atom (Core.Types.Str "Y")) appl_50
                                !appl_52 <- appl_51 `pseq` klCons (Core.Types.Atom (Core.Types.Str "X")) appl_51
                                !appl_53 <- appl_52 `pseq` klCons (Core.Types.Atom (Core.Types.Str "W")) appl_52
                                !appl_54 <- appl_53 `pseq` klCons (Core.Types.Atom (Core.Types.Str "V")) appl_53
                                !appl_55 <- appl_54 `pseq` klCons (Core.Types.Atom (Core.Types.Str "U")) appl_54
                                !appl_56 <- appl_55 `pseq` klCons (Core.Types.Atom (Core.Types.Str "T")) appl_55
                                !appl_57 <- appl_56 `pseq` klCons (Core.Types.Atom (Core.Types.Str "S")) appl_56
                                !appl_58 <- appl_57 `pseq` klCons (Core.Types.Atom (Core.Types.Str "R")) appl_57
                                !appl_59 <- appl_58 `pseq` klCons (Core.Types.Atom (Core.Types.Str "Q")) appl_58
                                !appl_60 <- appl_59 `pseq` klCons (Core.Types.Atom (Core.Types.Str "P")) appl_59
                                !appl_61 <- appl_60 `pseq` klCons (Core.Types.Atom (Core.Types.Str "O")) appl_60
                                !appl_62 <- appl_61 `pseq` klCons (Core.Types.Atom (Core.Types.Str "N")) appl_61
                                !appl_63 <- appl_62 `pseq` klCons (Core.Types.Atom (Core.Types.Str "M")) appl_62
                                !appl_64 <- appl_63 `pseq` klCons (Core.Types.Atom (Core.Types.Str "L")) appl_63
                                !appl_65 <- appl_64 `pseq` klCons (Core.Types.Atom (Core.Types.Str "K")) appl_64
                                !appl_66 <- appl_65 `pseq` klCons (Core.Types.Atom (Core.Types.Str "J")) appl_65
                                !appl_67 <- appl_66 `pseq` klCons (Core.Types.Atom (Core.Types.Str "I")) appl_66
                                !appl_68 <- appl_67 `pseq` klCons (Core.Types.Atom (Core.Types.Str "H")) appl_67
                                !appl_69 <- appl_68 `pseq` klCons (Core.Types.Atom (Core.Types.Str "G")) appl_68
                                !appl_70 <- appl_69 `pseq` klCons (Core.Types.Atom (Core.Types.Str "F")) appl_69
                                !appl_71 <- appl_70 `pseq` klCons (Core.Types.Atom (Core.Types.Str "E")) appl_70
                                !appl_72 <- appl_71 `pseq` klCons (Core.Types.Atom (Core.Types.Str "D")) appl_71
                                !appl_73 <- appl_72 `pseq` klCons (Core.Types.Atom (Core.Types.Str "C")) appl_72
                                !appl_74 <- appl_73 `pseq` klCons (Core.Types.Atom (Core.Types.Str "B")) appl_73
                                !appl_75 <- appl_74 `pseq` klCons (Core.Types.Atom (Core.Types.Str "A")) appl_74
                                kl_V2727 `pseq` (appl_75 `pseq` kl_elementP kl_V2727 appl_75)

kl_shen_alphanumsP :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_alphanumsP (!kl_V2729) = do let pat_cond_0 = do return (Atom (B True))
                                        pat_cond_1 = do !kl_if_2 <- kl_V2729 `pseq` kl_shen_PlusstringP kl_V2729
                                                        case kl_if_2 of
                                                            Atom (B (True)) -> do !appl_3 <- kl_V2729 `pseq` pos kl_V2729 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                  !kl_if_4 <- appl_3 `pseq` kl_shen_alphanumP appl_3
                                                                                  case kl_if_4 of
                                                                                      Atom (B (True)) -> do !appl_5 <- kl_V2729 `pseq` tlstr kl_V2729
                                                                                                            !kl_if_6 <- appl_5 `pseq` kl_shen_alphanumsP appl_5
                                                                                                            case kl_if_6 of
                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                _ -> throwError "if: expected boolean"
                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                      _ -> throwError "if: expected boolean"
                                                            Atom (B (False)) -> do do let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                      applyWrapper aw_7 [ApplC (wrapNamed "shen.alphanums?" kl_shen_alphanumsP)]
                                                            _ -> throwError "if: expected boolean"
                                     in case kl_V2729 of
                                            kl_V2729@(Atom (Str "")) -> pat_cond_0
                                            _ -> pat_cond_1

kl_shen_alphanumP :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_alphanumP (!kl_V2731) = do !kl_if_0 <- kl_V2731 `pseq` kl_shen_alphaP kl_V2731
                                   case kl_if_0 of
                                       Atom (B (True)) -> do return (Atom (B True))
                                       Atom (B (False)) -> do do !kl_if_1 <- kl_V2731 `pseq` kl_shen_digitP kl_V2731
                                                                 case kl_if_1 of
                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                     _ -> throwError "if: expected boolean"
                                       _ -> throwError "if: expected boolean"

kl_shen_digitP :: Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_digitP (!kl_V2733) = do let !appl_0 = Atom Nil
                                !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.Str "0")) appl_0
                                !appl_2 <- appl_1 `pseq` klCons (Core.Types.Atom (Core.Types.Str "9")) appl_1
                                !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.Str "8")) appl_2
                                !appl_4 <- appl_3 `pseq` klCons (Core.Types.Atom (Core.Types.Str "7")) appl_3
                                !appl_5 <- appl_4 `pseq` klCons (Core.Types.Atom (Core.Types.Str "6")) appl_4
                                !appl_6 <- appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.Str "5")) appl_5
                                !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.Str "4")) appl_6
                                !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.Str "3")) appl_7
                                !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.Str "2")) appl_8
                                !appl_10 <- appl_9 `pseq` klCons (Core.Types.Atom (Core.Types.Str "1")) appl_9
                                kl_V2733 `pseq` (appl_10 `pseq` kl_elementP kl_V2733 appl_10)

kl_variableP :: Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_variableP (!kl_V2735) = do !kl_if_0 <- kl_V2735 `pseq` kl_booleanP kl_V2735
                              !kl_if_1 <- case kl_if_0 of
                                              Atom (B (True)) -> do return (Atom (B True))
                                              Atom (B (False)) -> do do !kl_if_2 <- kl_V2735 `pseq` numberP kl_V2735
                                                                        !kl_if_3 <- case kl_if_2 of
                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                        Atom (B (False)) -> do do !kl_if_4 <- kl_V2735 `pseq` stringP kl_V2735
                                                                                                                  case kl_if_4 of
                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                        _ -> throwError "if: expected boolean"
                                                                        case kl_if_3 of
                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                            _ -> throwError "if: expected boolean"
                                              _ -> throwError "if: expected boolean"
                              case kl_if_1 of
                                  Atom (B (True)) -> do return (Atom (B False))
                                  Atom (B (False)) -> do do (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_String) -> do kl_String `pseq` kl_shen_analyse_variableP kl_String)))
                                                                !appl_6 <- kl_V2735 `pseq` str kl_V2735
                                                                appl_6 `pseq` applyWrapper appl_5 [appl_6]) `catchError` (\(!kl_E) -> do return (Atom (B False)))
                                  _ -> throwError "if: expected boolean"

kl_shen_analyse_variableP :: Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_analyse_variableP (!kl_V2737) = do !kl_if_0 <- kl_V2737 `pseq` kl_shen_PlusstringP kl_V2737
                                           case kl_if_0 of
                                               Atom (B (True)) -> do !appl_1 <- kl_V2737 `pseq` pos kl_V2737 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                     !kl_if_2 <- appl_1 `pseq` kl_shen_uppercaseP appl_1
                                                                     case kl_if_2 of
                                                                         Atom (B (True)) -> do !appl_3 <- kl_V2737 `pseq` tlstr kl_V2737
                                                                                               !kl_if_4 <- appl_3 `pseq` kl_shen_alphanumsP appl_3
                                                                                               case kl_if_4 of
                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                   _ -> throwError "if: expected boolean"
                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                         _ -> throwError "if: expected boolean"
                                               Atom (B (False)) -> do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                         applyWrapper aw_5 [ApplC (wrapNamed "shen.analyse-variable?" kl_shen_analyse_variableP)]
                                               _ -> throwError "if: expected boolean"

kl_shen_uppercaseP :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_uppercaseP (!kl_V2739) = do let !appl_0 = Atom Nil
                                    !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.Str "Z")) appl_0
                                    !appl_2 <- appl_1 `pseq` klCons (Core.Types.Atom (Core.Types.Str "Y")) appl_1
                                    !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.Str "X")) appl_2
                                    !appl_4 <- appl_3 `pseq` klCons (Core.Types.Atom (Core.Types.Str "W")) appl_3
                                    !appl_5 <- appl_4 `pseq` klCons (Core.Types.Atom (Core.Types.Str "V")) appl_4
                                    !appl_6 <- appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.Str "U")) appl_5
                                    !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.Str "T")) appl_6
                                    !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.Str "S")) appl_7
                                    !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.Str "R")) appl_8
                                    !appl_10 <- appl_9 `pseq` klCons (Core.Types.Atom (Core.Types.Str "Q")) appl_9
                                    !appl_11 <- appl_10 `pseq` klCons (Core.Types.Atom (Core.Types.Str "P")) appl_10
                                    !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.Str "O")) appl_11
                                    !appl_13 <- appl_12 `pseq` klCons (Core.Types.Atom (Core.Types.Str "N")) appl_12
                                    !appl_14 <- appl_13 `pseq` klCons (Core.Types.Atom (Core.Types.Str "M")) appl_13
                                    !appl_15 <- appl_14 `pseq` klCons (Core.Types.Atom (Core.Types.Str "L")) appl_14
                                    !appl_16 <- appl_15 `pseq` klCons (Core.Types.Atom (Core.Types.Str "K")) appl_15
                                    !appl_17 <- appl_16 `pseq` klCons (Core.Types.Atom (Core.Types.Str "J")) appl_16
                                    !appl_18 <- appl_17 `pseq` klCons (Core.Types.Atom (Core.Types.Str "I")) appl_17
                                    !appl_19 <- appl_18 `pseq` klCons (Core.Types.Atom (Core.Types.Str "H")) appl_18
                                    !appl_20 <- appl_19 `pseq` klCons (Core.Types.Atom (Core.Types.Str "G")) appl_19
                                    !appl_21 <- appl_20 `pseq` klCons (Core.Types.Atom (Core.Types.Str "F")) appl_20
                                    !appl_22 <- appl_21 `pseq` klCons (Core.Types.Atom (Core.Types.Str "E")) appl_21
                                    !appl_23 <- appl_22 `pseq` klCons (Core.Types.Atom (Core.Types.Str "D")) appl_22
                                    !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.Str "C")) appl_23
                                    !appl_25 <- appl_24 `pseq` klCons (Core.Types.Atom (Core.Types.Str "B")) appl_24
                                    !appl_26 <- appl_25 `pseq` klCons (Core.Types.Atom (Core.Types.Str "A")) appl_25
                                    kl_V2739 `pseq` (appl_26 `pseq` kl_elementP kl_V2739 appl_26)

kl_gensym :: Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_gensym (!kl_V2741) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*gensym*"))
                           !appl_1 <- appl_0 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_0
                           !appl_2 <- appl_1 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*gensym*")) appl_1
                           kl_V2741 `pseq` (appl_2 `pseq` kl_concat kl_V2741 appl_2)

kl_concat :: Core.Types.KLValue ->
             Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_concat (!kl_V2744) (!kl_V2745) = do !appl_0 <- kl_V2744 `pseq` str kl_V2744
                                       !appl_1 <- kl_V2745 `pseq` str kl_V2745
                                       !appl_2 <- appl_0 `pseq` (appl_1 `pseq` cn appl_0 appl_1)
                                       appl_2 `pseq` intern appl_2

kl_Atp :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_Atp (!kl_V2748) (!kl_V2749) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Vector) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Tag) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Fst) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Snd) -> do return kl_Vector)))
                                                                                                                                                                                                                                 !appl_4 <- kl_Vector `pseq` (kl_V2749 `pseq` addressTo kl_Vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) kl_V2749)
                                                                                                                                                                                                                                 appl_4 `pseq` applyWrapper appl_3 [appl_4])))
                                                                                                                                                                   !appl_5 <- kl_Vector `pseq` (kl_V2748 `pseq` addressTo kl_Vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V2748)
                                                                                                                                                                   appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                                     !appl_6 <- kl_Vector `pseq` addressTo kl_Vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) (Core.Types.Atom (Core.Types.UnboundSym "shen.tuple"))
                                                                                                     appl_6 `pseq` applyWrapper appl_1 [appl_6])))
                                    !appl_7 <- absvector (Core.Types.Atom (Core.Types.N (Core.Types.KI 3)))
                                    appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_fst :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_fst (!kl_V2751) = do kl_V2751 `pseq` addressFrom kl_V2751 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))

kl_snd :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_snd (!kl_V2753) = do kl_V2753 `pseq` addressFrom kl_V2753 (Core.Types.Atom (Core.Types.N (Core.Types.KI 2)))

kl_tupleP :: Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_tupleP (!kl_V2755) = do !kl_if_0 <- kl_V2755 `pseq` absvectorP kl_V2755
                           case kl_if_0 of
                               Atom (B (True)) -> do let !appl_1 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.UnboundSym "shen.not-tuple"))))
                                                     !appl_2 <- kl_V2755 `pseq` (appl_1 `pseq` kl_LB_addressDivor kl_V2755 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_1)
                                                     !kl_if_3 <- appl_2 `pseq` eq (Core.Types.Atom (Core.Types.UnboundSym "shen.tuple")) appl_2
                                                     case kl_if_3 of
                                                         Atom (B (True)) -> do return (Atom (B True))
                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                         _ -> throwError "if: expected boolean"
                               Atom (B (False)) -> do do return (Atom (B False))
                               _ -> throwError "if: expected boolean"

kl_append :: Core.Types.KLValue ->
             Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_append (!kl_V2758) (!kl_V2759) = do let !appl_0 = Atom Nil
                                       !kl_if_1 <- appl_0 `pseq` (kl_V2758 `pseq` eq appl_0 kl_V2758)
                                       case kl_if_1 of
                                           Atom (B (True)) -> do return kl_V2759
                                           Atom (B (False)) -> do let pat_cond_2 kl_V2758 kl_V2758h kl_V2758t = do !appl_3 <- kl_V2758t `pseq` (kl_V2759 `pseq` kl_append kl_V2758t kl_V2759)
                                                                                                                   kl_V2758h `pseq` (appl_3 `pseq` klCons kl_V2758h appl_3)
                                                                      pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                         applyWrapper aw_5 [ApplC (wrapNamed "append" kl_append)]
                                                                   in case kl_V2758 of
                                                                          !(kl_V2758@(Cons (!kl_V2758h)
                                                                                           (!kl_V2758t))) -> pat_cond_2 kl_V2758 kl_V2758h kl_V2758t
                                                                          _ -> pat_cond_4
                                           _ -> throwError "if: expected boolean"

kl_Atv :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_Atv (!kl_V2762) (!kl_V2763) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_NewVector) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_XPlusNewVector) -> do let pat_cond_3 = do return kl_XPlusNewVector
                                                                                                                                                                                                                                                     pat_cond_4 = do do kl_V2763 `pseq` (kl_Limit `pseq` (kl_XPlusNewVector `pseq` kl_shen_Atv_help kl_V2763 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_Limit kl_XPlusNewVector))
                                                                                                                                                                                                                                                  in case kl_Limit of
                                                                                                                                                                                                                                                         kl_Limit@(Atom (N (KI 0))) -> pat_cond_3
                                                                                                                                                                                                                                                         _ -> pat_cond_4)))
                                                                                                                                                                        !appl_5 <- kl_NewVector `pseq` (kl_V2762 `pseq` kl_vector_RB kl_NewVector (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V2762)
                                                                                                                                                                        appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                                    !appl_6 <- kl_Limit `pseq` add kl_Limit (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                    !appl_7 <- appl_6 `pseq` kl_vector appl_6
                                                                                                    appl_7 `pseq` applyWrapper appl_1 [appl_7])))
                                    !appl_8 <- kl_V2763 `pseq` kl_limit kl_V2763
                                    appl_8 `pseq` applyWrapper appl_0 [appl_8]

kl_shen_Atv_help :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_Atv_help (!kl_V2769) (!kl_V2770) (!kl_V2771) (!kl_V2772) = do !kl_if_0 <- kl_V2771 `pseq` (kl_V2770 `pseq` eq kl_V2771 kl_V2770)
                                                                      case kl_if_0 of
                                                                          Atom (B (True)) -> do !appl_1 <- kl_V2771 `pseq` add kl_V2771 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                kl_V2769 `pseq` (kl_V2772 `pseq` (kl_V2771 `pseq` (appl_1 `pseq` kl_shen_copyfromvector kl_V2769 kl_V2772 kl_V2771 appl_1)))
                                                                          Atom (B (False)) -> do do !appl_2 <- kl_V2770 `pseq` add kl_V2770 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                    !appl_3 <- kl_V2770 `pseq` add kl_V2770 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                    !appl_4 <- kl_V2769 `pseq` (kl_V2772 `pseq` (kl_V2770 `pseq` (appl_3 `pseq` kl_shen_copyfromvector kl_V2769 kl_V2772 kl_V2770 appl_3)))
                                                                                                    kl_V2769 `pseq` (appl_2 `pseq` (kl_V2771 `pseq` (appl_4 `pseq` kl_shen_Atv_help kl_V2769 appl_2 kl_V2771 appl_4)))
                                                                          _ -> throwError "if: expected boolean"

kl_shen_copyfromvector :: Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_copyfromvector (!kl_V2777) (!kl_V2778) (!kl_V2779) (!kl_V2780) = do (do !appl_0 <- kl_V2777 `pseq` (kl_V2779 `pseq` kl_LB_vector kl_V2777 kl_V2779)
                                                                                kl_V2778 `pseq` (kl_V2780 `pseq` (appl_0 `pseq` kl_vector_RB kl_V2778 kl_V2780 appl_0))) `catchError` (\(!kl_E) -> do return kl_V2778)

kl_hdv :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_hdv (!kl_V2782) = do let !appl_0 = ApplC (PL "thunk" (do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                            !appl_2 <- kl_V2782 `pseq` applyWrapper aw_1 [kl_V2782,
                                                                                                          Core.Types.Atom (Core.Types.Str "\n"),
                                                                                                          Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                            !appl_3 <- appl_2 `pseq` cn (Core.Types.Atom (Core.Types.Str "hdv needs a non-empty vector as an argument; not ")) appl_2
                                                            appl_3 `pseq` simpleError appl_3))
                        kl_V2782 `pseq` (appl_0 `pseq` kl_LB_vectorDivor kl_V2782 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_0)

kl_tlv :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_tlv (!kl_V2784) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do let pat_cond_1 = do simpleError (Core.Types.Atom (Core.Types.Str "cannot take the tail of the empty vector\n"))
                                                                                            pat_cond_2 = do do let pat_cond_3 = do kl_vector (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                   pat_cond_4 = do do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_NewVector) -> do !appl_6 <- kl_Limit `pseq` Primitives.subtract kl_Limit (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                                                                          !appl_7 <- appl_6 `pseq` kl_vector appl_6
                                                                                                                                                                                                          kl_V2784 `pseq` (kl_Limit `pseq` (appl_7 `pseq` kl_shen_tlv_help kl_V2784 (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) kl_Limit appl_7)))))
                                                                                                                                      !appl_8 <- kl_Limit `pseq` Primitives.subtract kl_Limit (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                      !appl_9 <- appl_8 `pseq` kl_vector appl_8
                                                                                                                                      appl_9 `pseq` applyWrapper appl_5 [appl_9]
                                                                                                                in case kl_Limit of
                                                                                                                       kl_Limit@(Atom (N (KI 1))) -> pat_cond_3
                                                                                                                       _ -> pat_cond_4
                                                                                         in case kl_Limit of
                                                                                                kl_Limit@(Atom (N (KI 0))) -> pat_cond_1
                                                                                                _ -> pat_cond_2)))
                        !appl_10 <- kl_V2784 `pseq` kl_limit kl_V2784
                        appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_tlv_help :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_tlv_help (!kl_V2790) (!kl_V2791) (!kl_V2792) (!kl_V2793) = do !kl_if_0 <- kl_V2792 `pseq` (kl_V2791 `pseq` eq kl_V2792 kl_V2791)
                                                                      case kl_if_0 of
                                                                          Atom (B (True)) -> do !appl_1 <- kl_V2792 `pseq` Primitives.subtract kl_V2792 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                kl_V2790 `pseq` (kl_V2793 `pseq` (kl_V2792 `pseq` (appl_1 `pseq` kl_shen_copyfromvector kl_V2790 kl_V2793 kl_V2792 appl_1)))
                                                                          Atom (B (False)) -> do do !appl_2 <- kl_V2791 `pseq` add kl_V2791 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                    !appl_3 <- kl_V2791 `pseq` Primitives.subtract kl_V2791 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                    !appl_4 <- kl_V2790 `pseq` (kl_V2793 `pseq` (kl_V2791 `pseq` (appl_3 `pseq` kl_shen_copyfromvector kl_V2790 kl_V2793 kl_V2791 appl_3)))
                                                                                                    kl_V2790 `pseq` (appl_2 `pseq` (kl_V2792 `pseq` (appl_4 `pseq` kl_shen_tlv_help kl_V2790 appl_2 kl_V2792 appl_4)))
                                                                          _ -> throwError "if: expected boolean"

kl_assoc :: Core.Types.KLValue ->
            Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_assoc (!kl_V2805) (!kl_V2806) = do let !appl_0 = Atom Nil
                                      !kl_if_1 <- appl_0 `pseq` (kl_V2806 `pseq` eq appl_0 kl_V2806)
                                      case kl_if_1 of
                                          Atom (B (True)) -> do return (Atom Nil)
                                          Atom (B (False)) -> do let pat_cond_2 kl_V2806 kl_V2806h kl_V2806hh kl_V2806ht kl_V2806t = do return kl_V2806h
                                                                     pat_cond_3 kl_V2806 kl_V2806h kl_V2806t = do kl_V2805 `pseq` (kl_V2806t `pseq` kl_assoc kl_V2805 kl_V2806t)
                                                                     pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                        applyWrapper aw_5 [ApplC (wrapNamed "assoc" kl_assoc)]
                                                                  in case kl_V2806 of
                                                                         !(kl_V2806@(Cons (!(kl_V2806h@(Cons (!kl_V2806hh)
                                                                                                             (!kl_V2806ht))))
                                                                                          (!kl_V2806t))) | eqCore kl_V2806hh kl_V2805 -> pat_cond_2 kl_V2806 kl_V2806h kl_V2806hh kl_V2806ht kl_V2806t
                                                                         !(kl_V2806@(Cons (!kl_V2806h)
                                                                                          (!kl_V2806t))) -> pat_cond_3 kl_V2806 kl_V2806h kl_V2806t
                                                                         _ -> pat_cond_4
                                          _ -> throwError "if: expected boolean"

kl_booleanP :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_booleanP (!kl_V2812) = do let pat_cond_0 = do return (Atom (B True))
                                 pat_cond_1 = do return (Atom (B True))
                                 pat_cond_2 = do do return (Atom (B False))
                              in case kl_V2812 of
                                     kl_V2812@(Atom (UnboundSym "true")) -> pat_cond_0
                                     kl_V2812@(Atom (B (True))) -> pat_cond_0
                                     kl_V2812@(Atom (UnboundSym "false")) -> pat_cond_1
                                     kl_V2812@(Atom (B (False))) -> pat_cond_1
                                     _ -> pat_cond_2

kl_nl :: Core.Types.KLValue ->
         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_nl (!kl_V2814) = do let pat_cond_0 = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                           pat_cond_1 = do do !appl_2 <- kl_stoutput
                                              let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                              !appl_4 <- appl_2 `pseq` applyWrapper aw_3 [Core.Types.Atom (Core.Types.Str "\n"),
                                                                                          appl_2]
                                              !appl_5 <- kl_V2814 `pseq` Primitives.subtract kl_V2814 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                              !appl_6 <- appl_5 `pseq` kl_nl appl_5
                                              appl_4 `pseq` (appl_6 `pseq` kl_do appl_4 appl_6)
                        in case kl_V2814 of
                               kl_V2814@(Atom (N (KI 0))) -> pat_cond_0
                               _ -> pat_cond_1

kl_difference :: Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_difference (!kl_V2819) (!kl_V2820) = do let !appl_0 = Atom Nil
                                           !kl_if_1 <- appl_0 `pseq` (kl_V2819 `pseq` eq appl_0 kl_V2819)
                                           case kl_if_1 of
                                               Atom (B (True)) -> do return (Atom Nil)
                                               Atom (B (False)) -> do let pat_cond_2 kl_V2819 kl_V2819h kl_V2819t = do !kl_if_3 <- kl_V2819h `pseq` (kl_V2820 `pseq` kl_elementP kl_V2819h kl_V2820)
                                                                                                                       case kl_if_3 of
                                                                                                                           Atom (B (True)) -> do kl_V2819t `pseq` (kl_V2820 `pseq` kl_difference kl_V2819t kl_V2820)
                                                                                                                           Atom (B (False)) -> do do !appl_4 <- kl_V2819t `pseq` (kl_V2820 `pseq` kl_difference kl_V2819t kl_V2820)
                                                                                                                                                     kl_V2819h `pseq` (appl_4 `pseq` klCons kl_V2819h appl_4)
                                                                                                                           _ -> throwError "if: expected boolean"
                                                                          pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                             applyWrapper aw_6 [ApplC (wrapNamed "difference" kl_difference)]
                                                                       in case kl_V2819 of
                                                                              !(kl_V2819@(Cons (!kl_V2819h)
                                                                                               (!kl_V2819t))) -> pat_cond_2 kl_V2819 kl_V2819h kl_V2819t
                                                                              _ -> pat_cond_5
                                               _ -> throwError "if: expected boolean"

kl_do :: Core.Types.KLValue ->
         Core.Types.KLValue ->
         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_do (!kl_V2823) (!kl_V2824) = do return kl_V2824

kl_elementP :: Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_elementP (!kl_V2836) (!kl_V2837) = do let !appl_0 = Atom Nil
                                         !kl_if_1 <- appl_0 `pseq` (kl_V2837 `pseq` eq appl_0 kl_V2837)
                                         case kl_if_1 of
                                             Atom (B (True)) -> do return (Atom (B False))
                                             Atom (B (False)) -> do let pat_cond_2 kl_V2837 kl_V2837h kl_V2837t = do return (Atom (B True))
                                                                        pat_cond_3 kl_V2837 kl_V2837h kl_V2837t = do kl_V2836 `pseq` (kl_V2837t `pseq` kl_elementP kl_V2836 kl_V2837t)
                                                                        pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                           applyWrapper aw_5 [ApplC (wrapNamed "element?" kl_elementP)]
                                                                     in case kl_V2837 of
                                                                            !(kl_V2837@(Cons (!kl_V2837h)
                                                                                             (!kl_V2837t))) | eqCore kl_V2837h kl_V2836 -> pat_cond_2 kl_V2837 kl_V2837h kl_V2837t
                                                                            !(kl_V2837@(Cons (!kl_V2837h)
                                                                                             (!kl_V2837t))) -> pat_cond_3 kl_V2837 kl_V2837h kl_V2837t
                                                                            _ -> pat_cond_4
                                             _ -> throwError "if: expected boolean"

kl_emptyP :: Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_emptyP (!kl_V2843) = do let !appl_0 = Atom Nil
                           !kl_if_1 <- appl_0 `pseq` (kl_V2843 `pseq` eq appl_0 kl_V2843)
                           case kl_if_1 of
                               Atom (B (True)) -> do return (Atom (B True))
                               Atom (B (False)) -> do do return (Atom (B False))
                               _ -> throwError "if: expected boolean"

kl_fix :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_fix (!kl_V2846) (!kl_V2847) = do !appl_0 <- kl_V2847 `pseq` applyWrapper kl_V2846 [kl_V2847]
                                    kl_V2846 `pseq` (kl_V2847 `pseq` (appl_0 `pseq` kl_shen_fix_help kl_V2846 kl_V2847 appl_0))

kl_shen_fix_help :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_fix_help (!kl_V2858) (!kl_V2859) (!kl_V2860) = do !kl_if_0 <- kl_V2860 `pseq` (kl_V2859 `pseq` eq kl_V2860 kl_V2859)
                                                          case kl_if_0 of
                                                              Atom (B (True)) -> do return kl_V2860
                                                              Atom (B (False)) -> do do !appl_1 <- kl_V2860 `pseq` applyWrapper kl_V2858 [kl_V2860]
                                                                                        kl_V2858 `pseq` (kl_V2860 `pseq` (appl_1 `pseq` kl_shen_fix_help kl_V2858 kl_V2860 appl_1))
                                                              _ -> throwError "if: expected boolean"

kl_dict :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict (!kl_V2862) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_D) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Tag) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Capacity) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Count) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Fill) -> do return kl_D)))
                                                                                                                                                                                                                                                                                      !appl_5 <- kl_V2862 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) kl_V2862
                                                                                                                                                                                                                                                                                      let !appl_6 = Atom Nil
                                                                                                                                                                                                                                                                                      !appl_7 <- kl_D `pseq` (appl_5 `pseq` (appl_6 `pseq` kl_shen_fillvector kl_D (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) appl_5 appl_6))
                                                                                                                                                                                                                                                                                      appl_7 `pseq` applyWrapper appl_4 [appl_7])))
                                                                                                                                                                                                                      !appl_8 <- kl_D `pseq` addressTo kl_D (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                                                      appl_8 `pseq` applyWrapper appl_3 [appl_8])))
                                                                                                                                                   !appl_9 <- kl_D `pseq` (kl_V2862 `pseq` addressTo kl_D (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V2862)
                                                                                                                                                   appl_9 `pseq` applyWrapper appl_2 [appl_9])))
                                                                                     !appl_10 <- kl_D `pseq` addressTo kl_D (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) (Core.Types.Atom (Core.Types.UnboundSym "shen.dictionary"))
                                                                                     appl_10 `pseq` applyWrapper appl_1 [appl_10])))
                         !appl_11 <- kl_V2862 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) kl_V2862
                         !appl_12 <- appl_11 `pseq` absvector appl_11
                         appl_12 `pseq` applyWrapper appl_0 [appl_12]

kl_dictP :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dictP (!kl_V2864) = do !kl_if_0 <- kl_V2864 `pseq` absvectorP kl_V2864
                          case kl_if_0 of
                              Atom (B (True)) -> do let !appl_1 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.UnboundSym "shen.not-dictionary"))))
                                                    !appl_2 <- kl_V2864 `pseq` (appl_1 `pseq` kl_LB_addressDivor kl_V2864 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_1)
                                                    !kl_if_3 <- appl_2 `pseq` eq appl_2 (Core.Types.Atom (Core.Types.UnboundSym "shen.dictionary"))
                                                    case kl_if_3 of
                                                        Atom (B (True)) -> do return (Atom (B True))
                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                        _ -> throwError "if: expected boolean"
                              Atom (B (False)) -> do do return (Atom (B False))
                              _ -> throwError "if: expected boolean"

kl_shen_dict_capacity :: Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_dict_capacity (!kl_V2866) = do kl_V2866 `pseq` addressFrom kl_V2866 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))

kl_dict_count :: Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict_count (!kl_V2868) = do kl_V2868 `pseq` addressFrom kl_V2868 (Core.Types.Atom (Core.Types.N (Core.Types.KI 2)))

kl_shen_dict_count_RB :: Core.Types.KLValue ->
                         Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_dict_count_RB (!kl_V2871) (!kl_V2872) = do kl_V2871 `pseq` (kl_V2872 `pseq` addressTo kl_V2871 (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) kl_V2872)

kl_shen_LB_dict_bucket :: Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_LB_dict_bucket (!kl_V2875) (!kl_V2876) = do !appl_0 <- kl_V2876 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) kl_V2876
                                                    kl_V2875 `pseq` (appl_0 `pseq` addressFrom kl_V2875 appl_0)

kl_shen_dict_bucket_RB :: Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_dict_bucket_RB (!kl_V2880) (!kl_V2881) (!kl_V2882) = do !appl_0 <- kl_V2881 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 3))) kl_V2881
                                                                kl_V2880 `pseq` (appl_0 `pseq` (kl_V2882 `pseq` addressTo kl_V2880 appl_0 kl_V2882))

kl_shen_set_key_entry_value :: Core.Types.KLValue ->
                               Core.Types.KLValue ->
                               Core.Types.KLValue ->
                               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_set_key_entry_value (!kl_V2889) (!kl_V2890) (!kl_V2891) = do let !appl_0 = Atom Nil
                                                                     !kl_if_1 <- appl_0 `pseq` (kl_V2891 `pseq` eq appl_0 kl_V2891)
                                                                     case kl_if_1 of
                                                                         Atom (B (True)) -> do !appl_2 <- kl_V2889 `pseq` (kl_V2890 `pseq` klCons kl_V2889 kl_V2890)
                                                                                               let !appl_3 = Atom Nil
                                                                                               appl_2 `pseq` (appl_3 `pseq` klCons appl_2 appl_3)
                                                                         Atom (B (False)) -> do let pat_cond_4 kl_V2891 kl_V2891h kl_V2891hh kl_V2891ht kl_V2891t = do !appl_5 <- kl_V2891hh `pseq` (kl_V2890 `pseq` klCons kl_V2891hh kl_V2890)
                                                                                                                                                                       appl_5 `pseq` (kl_V2891t `pseq` klCons appl_5 kl_V2891t)
                                                                                                    pat_cond_6 kl_V2891 kl_V2891h kl_V2891t = do !appl_7 <- kl_V2889 `pseq` (kl_V2890 `pseq` (kl_V2891t `pseq` kl_shen_set_key_entry_value kl_V2889 kl_V2890 kl_V2891t))
                                                                                                                                                 kl_V2891h `pseq` (appl_7 `pseq` klCons kl_V2891h appl_7)
                                                                                                    pat_cond_8 = do do let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                       applyWrapper aw_9 [ApplC (wrapNamed "shen.set-key-entry-value" kl_shen_set_key_entry_value)]
                                                                                                 in case kl_V2891 of
                                                                                                        !(kl_V2891@(Cons (!(kl_V2891h@(Cons (!kl_V2891hh)
                                                                                                                                            (!kl_V2891ht))))
                                                                                                                         (!kl_V2891t))) | eqCore kl_V2891hh kl_V2889 -> pat_cond_4 kl_V2891 kl_V2891h kl_V2891hh kl_V2891ht kl_V2891t
                                                                                                        !(kl_V2891@(Cons (!kl_V2891h)
                                                                                                                         (!kl_V2891t))) -> pat_cond_6 kl_V2891 kl_V2891h kl_V2891t
                                                                                                        _ -> pat_cond_8
                                                                         _ -> throwError "if: expected boolean"

kl_shen_remove_key_entry_value :: Core.Types.KLValue ->
                                  Core.Types.KLValue ->
                                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_remove_key_entry_value (!kl_V2897) (!kl_V2898) = do let !appl_0 = Atom Nil
                                                            !kl_if_1 <- appl_0 `pseq` (kl_V2898 `pseq` eq appl_0 kl_V2898)
                                                            case kl_if_1 of
                                                                Atom (B (True)) -> do return (Atom Nil)
                                                                Atom (B (False)) -> do let pat_cond_2 kl_V2898 kl_V2898h kl_V2898hh kl_V2898ht kl_V2898t = do return kl_V2898t
                                                                                           pat_cond_3 kl_V2898 kl_V2898h kl_V2898t = do !appl_4 <- kl_V2897 `pseq` (kl_V2898t `pseq` kl_shen_remove_key_entry_value kl_V2897 kl_V2898t)
                                                                                                                                        kl_V2898h `pseq` (appl_4 `pseq` klCons kl_V2898h appl_4)
                                                                                           pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                              applyWrapper aw_6 [ApplC (wrapNamed "shen.remove-key-entry-value" kl_shen_remove_key_entry_value)]
                                                                                        in case kl_V2898 of
                                                                                               !(kl_V2898@(Cons (!(kl_V2898h@(Cons (!kl_V2898hh)
                                                                                                                                   (!kl_V2898ht))))
                                                                                                                (!kl_V2898t))) | eqCore kl_V2898hh kl_V2897 -> pat_cond_2 kl_V2898 kl_V2898h kl_V2898hh kl_V2898ht kl_V2898t
                                                                                               !(kl_V2898@(Cons (!kl_V2898h)
                                                                                                                (!kl_V2898t))) -> pat_cond_3 kl_V2898 kl_V2898h kl_V2898t
                                                                                               _ -> pat_cond_5
                                                                _ -> throwError "if: expected boolean"

kl_shen_dict_update_count :: Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_dict_update_count (!kl_V2902) (!kl_V2903) (!kl_V2904) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Diff) -> do !appl_1 <- kl_V2902 `pseq` kl_dict_count kl_V2902
                                                                                                                                  !appl_2 <- kl_Diff `pseq` (appl_1 `pseq` add kl_Diff appl_1)
                                                                                                                                  kl_V2902 `pseq` (appl_2 `pseq` kl_shen_dict_count_RB kl_V2902 appl_2))))
                                                                   !appl_3 <- kl_V2904 `pseq` kl_length kl_V2904
                                                                   !appl_4 <- kl_V2903 `pseq` kl_length kl_V2903
                                                                   !appl_5 <- appl_3 `pseq` (appl_4 `pseq` Primitives.subtract appl_3 appl_4)
                                                                   appl_5 `pseq` applyWrapper appl_0 [appl_5]

kl_dict_RB :: Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict_RB (!kl_V2908) (!kl_V2909) (!kl_V2910) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Bucket) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_NewBucket) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Change) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Count) -> do return kl_V2910)))
                                                                                                                                                                                                                                                                                                                      !appl_5 <- kl_V2908 `pseq` (kl_Bucket `pseq` (kl_NewBucket `pseq` kl_shen_dict_update_count kl_V2908 kl_Bucket kl_NewBucket))
                                                                                                                                                                                                                                                                                                                      appl_5 `pseq` applyWrapper appl_4 [appl_5])))
                                                                                                                                                                                                                                                     !appl_6 <- kl_V2908 `pseq` (kl_N `pseq` (kl_NewBucket `pseq` kl_shen_dict_bucket_RB kl_V2908 kl_N kl_NewBucket))
                                                                                                                                                                                                                                                     appl_6 `pseq` applyWrapper appl_3 [appl_6])))
                                                                                                                                                                                 !appl_7 <- kl_V2909 `pseq` (kl_V2910 `pseq` (kl_Bucket `pseq` kl_shen_set_key_entry_value kl_V2909 kl_V2910 kl_Bucket))
                                                                                                                                                                                 appl_7 `pseq` applyWrapper appl_2 [appl_7])))
                                                                                                                !appl_8 <- kl_V2908 `pseq` (kl_N `pseq` kl_shen_LB_dict_bucket kl_V2908 kl_N)
                                                                                                                appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                                                    !appl_9 <- kl_V2908 `pseq` kl_shen_dict_capacity kl_V2908
                                                    !appl_10 <- kl_V2909 `pseq` (appl_9 `pseq` kl_hash kl_V2909 appl_9)
                                                    appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_LB_dictDivor :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LB_dictDivor (!kl_V2914) (!kl_V2915) (!kl_V2916) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Bucket) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Result) -> do !kl_if_3 <- kl_Result `pseq` kl_emptyP kl_Result
                                                                                                                                                                                                                                                       case kl_if_3 of
                                                                                                                                                                                                                                                           Atom (B (True)) -> do kl_V2916 `pseq` kl_thaw kl_V2916
                                                                                                                                                                                                                                                           Atom (B (False)) -> do do kl_Result `pseq` tl kl_Result
                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean")))
                                                                                                                                                                                      !appl_4 <- kl_V2915 `pseq` (kl_Bucket `pseq` kl_assoc kl_V2915 kl_Bucket)
                                                                                                                                                                                      appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                                     !appl_5 <- kl_V2914 `pseq` (kl_N `pseq` kl_shen_LB_dict_bucket kl_V2914 kl_N)
                                                                                                                     appl_5 `pseq` applyWrapper appl_1 [appl_5])))
                                                         !appl_6 <- kl_V2914 `pseq` kl_shen_dict_capacity kl_V2914
                                                         !appl_7 <- kl_V2915 `pseq` (appl_6 `pseq` kl_hash kl_V2915 appl_6)
                                                         appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_LB_dict :: Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_LB_dict (!kl_V2919) (!kl_V2920) = do let !appl_0 = ApplC (PL "thunk" (do simpleError (Core.Types.Atom (Core.Types.Str "value not found\n"))))
                                        kl_V2919 `pseq` (kl_V2920 `pseq` (appl_0 `pseq` kl_LB_dictDivor kl_V2919 kl_V2920 appl_0))

kl_dict_rm :: Core.Types.KLValue ->
              Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict_rm (!kl_V2923) (!kl_V2924) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Bucket) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_NewBucket) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Change) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Count) -> do return kl_V2924)))
                                                                                                                                                                                                                                                                                                          !appl_5 <- kl_V2923 `pseq` (kl_Bucket `pseq` (kl_NewBucket `pseq` kl_shen_dict_update_count kl_V2923 kl_Bucket kl_NewBucket))
                                                                                                                                                                                                                                                                                                          appl_5 `pseq` applyWrapper appl_4 [appl_5])))
                                                                                                                                                                                                                                         !appl_6 <- kl_V2923 `pseq` (kl_N `pseq` (kl_NewBucket `pseq` kl_shen_dict_bucket_RB kl_V2923 kl_N kl_NewBucket))
                                                                                                                                                                                                                                         appl_6 `pseq` applyWrapper appl_3 [appl_6])))
                                                                                                                                                                     !appl_7 <- kl_V2924 `pseq` (kl_Bucket `pseq` kl_shen_remove_key_entry_value kl_V2924 kl_Bucket)
                                                                                                                                                                     appl_7 `pseq` applyWrapper appl_2 [appl_7])))
                                                                                                    !appl_8 <- kl_V2923 `pseq` (kl_N `pseq` kl_shen_LB_dict_bucket kl_V2923 kl_N)
                                                                                                    appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                                        !appl_9 <- kl_V2923 `pseq` kl_shen_dict_capacity kl_V2923
                                        !appl_10 <- kl_V2924 `pseq` (appl_9 `pseq` kl_hash kl_V2924 appl_9)
                                        appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_dict_fold :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict_fold (!kl_V2928) (!kl_V2929) (!kl_V2930) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do kl_V2928 `pseq` (kl_V2929 `pseq` (kl_V2930 `pseq` (kl_Limit `pseq` kl_shen_dict_fold_h kl_V2928 kl_V2929 kl_V2930 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) kl_Limit))))))
                                                      !appl_1 <- kl_V2929 `pseq` kl_shen_dict_capacity kl_V2929
                                                      appl_1 `pseq` applyWrapper appl_0 [appl_1]

kl_shen_dict_fold_h :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_dict_fold_h (!kl_V2937) (!kl_V2938) (!kl_V2939) (!kl_V2940) (!kl_V2941) = do !kl_if_0 <- kl_V2941 `pseq` (kl_V2940 `pseq` eq kl_V2941 kl_V2940)
                                                                                     case kl_if_0 of
                                                                                         Atom (B (True)) -> do return kl_V2939
                                                                                         Atom (B (False)) -> do do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_B) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Acc) -> do !appl_3 <- kl_V2940 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V2940
                                                                                                                                                                                                                                             kl_V2937 `pseq` (kl_V2938 `pseq` (kl_Acc `pseq` (appl_3 `pseq` (kl_V2941 `pseq` kl_shen_dict_fold_h kl_V2937 kl_V2938 kl_Acc appl_3 kl_V2941)))))))
                                                                                                                                                                               !appl_4 <- kl_V2937 `pseq` (kl_B `pseq` (kl_V2939 `pseq` kl_shen_bucket_fold kl_V2937 kl_B kl_V2939))
                                                                                                                                                                               appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                                   !appl_5 <- kl_V2938 `pseq` (kl_V2940 `pseq` kl_shen_LB_dict_bucket kl_V2938 kl_V2940)
                                                                                                                   appl_5 `pseq` applyWrapper appl_1 [appl_5]
                                                                                         _ -> throwError "if: expected boolean"

kl_shen_bucket_fold :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_bucket_fold (!kl_V2945) (!kl_V2946) (!kl_V2947) = do let !appl_0 = Atom Nil
                                                             !kl_if_1 <- appl_0 `pseq` (kl_V2946 `pseq` eq appl_0 kl_V2946)
                                                             case kl_if_1 of
                                                                 Atom (B (True)) -> do return kl_V2947
                                                                 Atom (B (False)) -> do let pat_cond_2 kl_V2946 kl_V2946h kl_V2946hh kl_V2946ht kl_V2946t = do !appl_3 <- kl_V2945 `pseq` (kl_V2946t `pseq` (kl_V2947 `pseq` kl_fold_right kl_V2945 kl_V2946t kl_V2947))
                                                                                                                                                               kl_V2946hh `pseq` (kl_V2946ht `pseq` (appl_3 `pseq` applyWrapper kl_V2945 [kl_V2946hh,
                                                                                                                                                                                                                                          kl_V2946ht,
                                                                                                                                                                                                                                          appl_3]))
                                                                                            pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                               applyWrapper aw_5 [ApplC (wrapNamed "shen.bucket-fold" kl_shen_bucket_fold)]
                                                                                         in case kl_V2946 of
                                                                                                !(kl_V2946@(Cons (!(kl_V2946h@(Cons (!kl_V2946hh)
                                                                                                                                    (!kl_V2946ht))))
                                                                                                                 (!kl_V2946t))) -> pat_cond_2 kl_V2946 kl_V2946h kl_V2946hh kl_V2946ht kl_V2946t
                                                                                                _ -> pat_cond_4
                                                                 _ -> throwError "if: expected boolean"

kl_dict_keys :: Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict_keys (!kl_V2949) = kl_dict_fold (ApplC (wrapNamed "lambda" (\k (_ :: Core.Types.KLValue) (acc :: Core.Types.KLValue) -> klCons k acc))) kl_V2949 (Atom Nil)

kl_dict_values :: Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_dict_values (!kl_V2951) = kl_dict_fold (ApplC (wrapNamed "lambda" (\(_ :: Core.Types.KLValue) v (acc :: Core.Types.KLValue) -> klCons v acc))) kl_V2951 (Atom Nil)

kl_put :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_put (!kl_V2956) (!kl_V2957) (!kl_V2958) (!kl_V2959) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Curr) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Added) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Update) -> do return kl_V2958)))
                                                                                                                                                                                           !appl_3 <- kl_V2959 `pseq` (kl_V2956 `pseq` (kl_Added `pseq` kl_dict_RB kl_V2959 kl_V2956 kl_Added))
                                                                                                                                                                                           appl_3 `pseq` applyWrapper appl_2 [appl_3])))
                                                                                                                           !appl_4 <- kl_V2957 `pseq` (kl_V2958 `pseq` (kl_Curr `pseq` kl_shen_set_key_entry_value kl_V2957 kl_V2958 kl_Curr))
                                                                                                                           appl_4 `pseq` applyWrapper appl_1 [appl_4])))
                                                            let !appl_5 = ApplC (PL "thunk" (do return (Atom Nil)))
                                                            !appl_6 <- kl_V2959 `pseq` (kl_V2956 `pseq` (appl_5 `pseq` kl_LB_dictDivor kl_V2959 kl_V2956 appl_5))
                                                            appl_6 `pseq` applyWrapper appl_0 [appl_6]

kl_unput :: Core.Types.KLValue ->
            Core.Types.KLValue ->
            Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_unput (!kl_V2963) (!kl_V2964) (!kl_V2965) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Curr) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Removed) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Update) -> do return kl_V2963)))
                                                                                                                                                                                   !appl_3 <- kl_V2965 `pseq` (kl_V2963 `pseq` (kl_Removed `pseq` kl_dict_RB kl_V2965 kl_V2963 kl_Removed))
                                                                                                                                                                                   appl_3 `pseq` applyWrapper appl_2 [appl_3])))
                                                                                                                 !appl_4 <- kl_V2964 `pseq` (kl_Curr `pseq` kl_shen_remove_key_entry_value kl_V2964 kl_Curr)
                                                                                                                 appl_4 `pseq` applyWrapper appl_1 [appl_4])))
                                                  let !appl_5 = ApplC (PL "thunk" (do return (Atom Nil)))
                                                  !appl_6 <- kl_V2965 `pseq` (kl_V2963 `pseq` (appl_5 `pseq` kl_LB_dictDivor kl_V2965 kl_V2963 appl_5))
                                                  appl_6 `pseq` applyWrapper appl_0 [appl_6]

kl_getDivor :: Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_getDivor (!kl_V2970) (!kl_V2971) (!kl_V2972) (!kl_V2973) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Result) -> do !kl_if_2 <- kl_Result `pseq` kl_emptyP kl_Result
                                                                                                                                                                                                  case kl_if_2 of
                                                                                                                                                                                                      Atom (B (True)) -> do kl_V2972 `pseq` kl_thaw kl_V2972
                                                                                                                                                                                                      Atom (B (False)) -> do do kl_Result `pseq` tl kl_Result
                                                                                                                                                                                                      _ -> throwError "if: expected boolean")))
                                                                                                                                 !appl_3 <- kl_V2971 `pseq` (kl_Entry `pseq` kl_assoc kl_V2971 kl_Entry)
                                                                                                                                 appl_3 `pseq` applyWrapper appl_1 [appl_3])))
                                                                 let !appl_4 = ApplC (PL "thunk" (do return (Atom Nil)))
                                                                 !appl_5 <- kl_V2973 `pseq` (kl_V2970 `pseq` (appl_4 `pseq` kl_LB_dictDivor kl_V2973 kl_V2970 appl_4))
                                                                 appl_5 `pseq` applyWrapper appl_0 [appl_5]

kl_get :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_get (!kl_V2977) (!kl_V2978) (!kl_V2979) = do let !appl_0 = ApplC (PL "thunk" (do simpleError (Core.Types.Atom (Core.Types.Str "value not found\n"))))
                                                kl_V2977 `pseq` (kl_V2978 `pseq` (appl_0 `pseq` (kl_V2979 `pseq` kl_getDivor kl_V2977 kl_V2978 appl_0 kl_V2979)))

kl_hash :: Core.Types.KLValue ->
           Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_hash (!kl_V2982) (!kl_V2983) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` stringToN kl_X)))
                                     !appl_1 <- kl_V2982 `pseq` kl_explode kl_V2982
                                     !appl_2 <- appl_0 `pseq` (appl_1 `pseq` kl_map appl_0 appl_1)
                                     !appl_3 <- appl_2 `pseq` kl_sum appl_2
                                     appl_3 `pseq` (kl_V2983 `pseq` kl_shen_mod appl_3 kl_V2983)

kl_shen_mod :: Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_mod (!kl_V2986) (!kl_V2987) = do let !appl_0 = Atom Nil
                                         !appl_1 <- kl_V2987 `pseq` (appl_0 `pseq` klCons kl_V2987 appl_0)
                                         !appl_2 <- kl_V2986 `pseq` (appl_1 `pseq` kl_shen_multiples kl_V2986 appl_1)
                                         kl_V2986 `pseq` (appl_2 `pseq` kl_shen_modh kl_V2986 appl_2)

kl_shen_multiples :: Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_multiples (!kl_V2990) (!kl_V2991) = do !kl_if_0 <- let pat_cond_1 kl_V2991 kl_V2991h kl_V2991t = do !kl_if_2 <- kl_V2991h `pseq` (kl_V2990 `pseq` greaterThan kl_V2991h kl_V2990)
                                                                                                            case kl_if_2 of
                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                _ -> throwError "if: expected boolean"
                                                               pat_cond_3 = do do return (Atom (B False))
                                                            in case kl_V2991 of
                                                                   !(kl_V2991@(Cons (!kl_V2991h)
                                                                                    (!kl_V2991t))) -> pat_cond_1 kl_V2991 kl_V2991h kl_V2991t
                                                                   _ -> pat_cond_3
                                               case kl_if_0 of
                                                   Atom (B (True)) -> do kl_V2991 `pseq` tl kl_V2991
                                                   Atom (B (False)) -> do let pat_cond_4 kl_V2991 kl_V2991h kl_V2991t = do !appl_5 <- kl_V2991h `pseq` multiply (Core.Types.Atom (Core.Types.N (Core.Types.KI 2))) kl_V2991h
                                                                                                                           !appl_6 <- appl_5 `pseq` (kl_V2991 `pseq` klCons appl_5 kl_V2991)
                                                                                                                           kl_V2990 `pseq` (appl_6 `pseq` kl_shen_multiples kl_V2990 appl_6)
                                                                              pat_cond_7 = do do let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                 applyWrapper aw_8 [ApplC (wrapNamed "shen.multiples" kl_shen_multiples)]
                                                                           in case kl_V2991 of
                                                                                  !(kl_V2991@(Cons (!kl_V2991h)
                                                                                                   (!kl_V2991t))) -> pat_cond_4 kl_V2991 kl_V2991h kl_V2991t
                                                                                  _ -> pat_cond_7
                                                   _ -> throwError "if: expected boolean"

kl_shen_modh :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_modh (!kl_V2996) (!kl_V2997) = do let pat_cond_0 = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                              pat_cond_1 = do let !appl_2 = Atom Nil
                                                              !kl_if_3 <- appl_2 `pseq` (kl_V2997 `pseq` eq appl_2 kl_V2997)
                                                              case kl_if_3 of
                                                                  Atom (B (True)) -> do return kl_V2996
                                                                  Atom (B (False)) -> do !kl_if_4 <- let pat_cond_5 kl_V2997 kl_V2997h kl_V2997t = do !kl_if_6 <- kl_V2997h `pseq` (kl_V2996 `pseq` greaterThan kl_V2997h kl_V2996)
                                                                                                                                                      case kl_if_6 of
                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                         pat_cond_7 = do do return (Atom (B False))
                                                                                                      in case kl_V2997 of
                                                                                                             !(kl_V2997@(Cons (!kl_V2997h)
                                                                                                                              (!kl_V2997t))) -> pat_cond_5 kl_V2997 kl_V2997h kl_V2997t
                                                                                                             _ -> pat_cond_7
                                                                                         case kl_if_4 of
                                                                                             Atom (B (True)) -> do !appl_8 <- kl_V2997 `pseq` tl kl_V2997
                                                                                                                   !kl_if_9 <- appl_8 `pseq` kl_emptyP appl_8
                                                                                                                   case kl_if_9 of
                                                                                                                       Atom (B (True)) -> do return kl_V2996
                                                                                                                       Atom (B (False)) -> do do !appl_10 <- kl_V2997 `pseq` tl kl_V2997
                                                                                                                                                 kl_V2996 `pseq` (appl_10 `pseq` kl_shen_modh kl_V2996 appl_10)
                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                             Atom (B (False)) -> do let pat_cond_11 kl_V2997 kl_V2997h kl_V2997t = do !appl_12 <- kl_V2996 `pseq` (kl_V2997h `pseq` Primitives.subtract kl_V2996 kl_V2997h)
                                                                                                                                                                      appl_12 `pseq` (kl_V2997 `pseq` kl_shen_modh appl_12 kl_V2997)
                                                                                                                        pat_cond_13 = do do let !aw_14 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                            applyWrapper aw_14 [ApplC (wrapNamed "shen.modh" kl_shen_modh)]
                                                                                                                     in case kl_V2997 of
                                                                                                                            !(kl_V2997@(Cons (!kl_V2997h)
                                                                                                                                             (!kl_V2997t))) -> pat_cond_11 kl_V2997 kl_V2997h kl_V2997t
                                                                                                                            _ -> pat_cond_13
                                                                                             _ -> throwError "if: expected boolean"
                                                                  _ -> throwError "if: expected boolean"
                                           in case kl_V2996 of
                                                  kl_V2996@(Atom (N (KI 0))) -> pat_cond_0
                                                  _ -> pat_cond_1

kl_sum :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_sum (!kl_V2999) = do let !appl_0 = Atom Nil
                        !kl_if_1 <- appl_0 `pseq` (kl_V2999 `pseq` eq appl_0 kl_V2999)
                        case kl_if_1 of
                            Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                            Atom (B (False)) -> do let pat_cond_2 kl_V2999 kl_V2999h kl_V2999t = do !appl_3 <- kl_V2999t `pseq` kl_sum kl_V2999t
                                                                                                    kl_V2999h `pseq` (appl_3 `pseq` add kl_V2999h appl_3)
                                                       pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                          applyWrapper aw_5 [ApplC (wrapNamed "sum" kl_sum)]
                                                    in case kl_V2999 of
                                                           !(kl_V2999@(Cons (!kl_V2999h)
                                                                            (!kl_V2999t))) -> pat_cond_2 kl_V2999 kl_V2999h kl_V2999t
                                                           _ -> pat_cond_4
                            _ -> throwError "if: expected boolean"

kl_head :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_head (!kl_V3007) = do let pat_cond_0 kl_V3007 kl_V3007h kl_V3007t = do return kl_V3007h
                             pat_cond_1 = do do simpleError (Core.Types.Atom (Core.Types.Str "head expects a non-empty list"))
                          in case kl_V3007 of
                                 !(kl_V3007@(Cons (!kl_V3007h)
                                                  (!kl_V3007t))) -> pat_cond_0 kl_V3007 kl_V3007h kl_V3007t
                                 _ -> pat_cond_1

kl_tail :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_tail (!kl_V3015) = do let pat_cond_0 kl_V3015 kl_V3015h kl_V3015t = do return kl_V3015t
                             pat_cond_1 = do do simpleError (Core.Types.Atom (Core.Types.Str "tail expects a non-empty list"))
                          in case kl_V3015 of
                                 !(kl_V3015@(Cons (!kl_V3015h)
                                                  (!kl_V3015t))) -> pat_cond_0 kl_V3015 kl_V3015h kl_V3015t
                                 _ -> pat_cond_1

kl_hdstr :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_hdstr (!kl_V3017) = do kl_V3017 `pseq` pos kl_V3017 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))

kl_intersection :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_intersection (!kl_V3022) (!kl_V3023) = do let !appl_0 = Atom Nil
                                             !kl_if_1 <- appl_0 `pseq` (kl_V3022 `pseq` eq appl_0 kl_V3022)
                                             case kl_if_1 of
                                                 Atom (B (True)) -> do return (Atom Nil)
                                                 Atom (B (False)) -> do let pat_cond_2 kl_V3022 kl_V3022h kl_V3022t = do !kl_if_3 <- kl_V3022h `pseq` (kl_V3023 `pseq` kl_elementP kl_V3022h kl_V3023)
                                                                                                                         case kl_if_3 of
                                                                                                                             Atom (B (True)) -> do !appl_4 <- kl_V3022t `pseq` (kl_V3023 `pseq` kl_intersection kl_V3022t kl_V3023)
                                                                                                                                                   kl_V3022h `pseq` (appl_4 `pseq` klCons kl_V3022h appl_4)
                                                                                                                             Atom (B (False)) -> do do kl_V3022t `pseq` (kl_V3023 `pseq` kl_intersection kl_V3022t kl_V3023)
                                                                                                                             _ -> throwError "if: expected boolean"
                                                                            pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                               applyWrapper aw_6 [ApplC (wrapNamed "intersection" kl_intersection)]
                                                                         in case kl_V3022 of
                                                                                !(kl_V3022@(Cons (!kl_V3022h)
                                                                                                 (!kl_V3022t))) -> pat_cond_2 kl_V3022 kl_V3022h kl_V3022t
                                                                                _ -> pat_cond_5
                                                 _ -> throwError "if: expected boolean"

kl_reverse :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_reverse (!kl_V3025) = do let !appl_0 = Atom Nil
                            kl_V3025 `pseq` (appl_0 `pseq` kl_shen_reverse_help kl_V3025 appl_0)

kl_shen_reverse_help :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_reverse_help (!kl_V3028) (!kl_V3029) = do let !appl_0 = Atom Nil
                                                  !kl_if_1 <- appl_0 `pseq` (kl_V3028 `pseq` eq appl_0 kl_V3028)
                                                  case kl_if_1 of
                                                      Atom (B (True)) -> do return kl_V3029
                                                      Atom (B (False)) -> do let pat_cond_2 kl_V3028 kl_V3028h kl_V3028t = do !appl_3 <- kl_V3028h `pseq` (kl_V3029 `pseq` klCons kl_V3028h kl_V3029)
                                                                                                                              kl_V3028t `pseq` (appl_3 `pseq` kl_shen_reverse_help kl_V3028t appl_3)
                                                                                 pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                    applyWrapper aw_5 [ApplC (wrapNamed "shen.reverse_help" kl_shen_reverse_help)]
                                                                              in case kl_V3028 of
                                                                                     !(kl_V3028@(Cons (!kl_V3028h)
                                                                                                      (!kl_V3028t))) -> pat_cond_2 kl_V3028 kl_V3028h kl_V3028t
                                                                                     _ -> pat_cond_4
                                                      _ -> throwError "if: expected boolean"

kl_union :: Core.Types.KLValue ->
            Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_union (!kl_V3032) (!kl_V3033) = do let !appl_0 = Atom Nil
                                      !kl_if_1 <- appl_0 `pseq` (kl_V3032 `pseq` eq appl_0 kl_V3032)
                                      case kl_if_1 of
                                          Atom (B (True)) -> do return kl_V3033
                                          Atom (B (False)) -> do let pat_cond_2 kl_V3032 kl_V3032h kl_V3032t = do !kl_if_3 <- kl_V3032h `pseq` (kl_V3033 `pseq` kl_elementP kl_V3032h kl_V3033)
                                                                                                                  case kl_if_3 of
                                                                                                                      Atom (B (True)) -> do kl_V3032t `pseq` (kl_V3033 `pseq` kl_union kl_V3032t kl_V3033)
                                                                                                                      Atom (B (False)) -> do do !appl_4 <- kl_V3032t `pseq` (kl_V3033 `pseq` kl_union kl_V3032t kl_V3033)
                                                                                                                                                kl_V3032h `pseq` (appl_4 `pseq` klCons kl_V3032h appl_4)
                                                                                                                      _ -> throwError "if: expected boolean"
                                                                     pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                        applyWrapper aw_6 [ApplC (wrapNamed "union" kl_union)]
                                                                  in case kl_V3032 of
                                                                         !(kl_V3032@(Cons (!kl_V3032h)
                                                                                          (!kl_V3032t))) -> pat_cond_2 kl_V3032 kl_V3032h kl_V3032t
                                                                         _ -> pat_cond_5
                                          _ -> throwError "if: expected boolean"

kl_y_or_nP :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_y_or_nP (!kl_V3035) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Message) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Y_or_N) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Input) -> do let pat_cond_3 = do return (Atom (B True))
                                                                                                                                                                                                                                   pat_cond_4 = do do let pat_cond_5 = do return (Atom (B False))
                                                                                                                                                                                                                                                          pat_cond_6 = do do !appl_7 <- kl_stoutput
                                                                                                                                                                                                                                                                             let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                             !appl_9 <- appl_7 `pseq` applyWrapper aw_8 [Core.Types.Atom (Core.Types.Str "please answer y or n\n"),
                                                                                                                                                                                                                                                                                                                         appl_7]
                                                                                                                                                                                                                                                                             !appl_10 <- kl_V3035 `pseq` kl_y_or_nP kl_V3035
                                                                                                                                                                                                                                                                             appl_9 `pseq` (appl_10 `pseq` kl_do appl_9 appl_10)
                                                                                                                                                                                                                                                       in case kl_Input of
                                                                                                                                                                                                                                                              kl_Input@(Atom (Str "n")) -> pat_cond_5
                                                                                                                                                                                                                                                              _ -> pat_cond_6
                                                                                                                                                                                                                                in case kl_Input of
                                                                                                                                                                                                                                       kl_Input@(Atom (Str "y")) -> pat_cond_3
                                                                                                                                                                                                                                       _ -> pat_cond_4)))
                                                                                                                                                               !appl_11 <- kl_stinput
                                                                                                                                                               let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "read")
                                                                                                                                                               !appl_13 <- appl_11 `pseq` applyWrapper aw_12 [appl_11]
                                                                                                                                                               let !aw_14 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                               !appl_15 <- appl_13 `pseq` applyWrapper aw_14 [appl_13,
                                                                                                                                                                                                              Core.Types.Atom (Core.Types.Str ""),
                                                                                                                                                                                                              Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                                                                                                                               appl_15 `pseq` applyWrapper appl_2 [appl_15])))
                                                                                              !appl_16 <- kl_stoutput
                                                                                              let !aw_17 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                              !appl_18 <- appl_16 `pseq` applyWrapper aw_17 [Core.Types.Atom (Core.Types.Str " (y/n) "),
                                                                                                                                             appl_16]
                                                                                              appl_18 `pseq` applyWrapper appl_1 [appl_18])))
                            let !aw_19 = Core.Types.Atom (Core.Types.UnboundSym "shen.proc-nl")
                            !appl_20 <- kl_V3035 `pseq` applyWrapper aw_19 [kl_V3035]
                            !appl_21 <- kl_stoutput
                            let !aw_22 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                            !appl_23 <- appl_20 `pseq` (appl_21 `pseq` applyWrapper aw_22 [appl_20,
                                                                                           appl_21])
                            appl_23 `pseq` applyWrapper appl_0 [appl_23]

kl_not :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_not (!kl_V3037) = do case kl_V3037 of
                            Atom (B (True)) -> do return (Atom (B False))
                            Atom (B (False)) -> do do return (Atom (B True))
                            _ -> throwError "if: expected boolean"

kl_subst :: Core.Types.KLValue ->
            Core.Types.KLValue ->
            Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_subst (!kl_V3050) (!kl_V3051) (!kl_V3052) = do !kl_if_0 <- kl_V3052 `pseq` (kl_V3051 `pseq` eq kl_V3052 kl_V3051)
                                                  case kl_if_0 of
                                                      Atom (B (True)) -> do return kl_V3050
                                                      Atom (B (False)) -> do let pat_cond_1 kl_V3052 kl_V3052h kl_V3052t = do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_W) -> do kl_V3050 `pseq` (kl_V3051 `pseq` (kl_W `pseq` kl_subst kl_V3050 kl_V3051 kl_W)))))
                                                                                                                              appl_2 `pseq` (kl_V3052 `pseq` kl_map appl_2 kl_V3052)
                                                                                 pat_cond_3 = do do return kl_V3052
                                                                              in case kl_V3052 of
                                                                                     !(kl_V3052@(Cons (!kl_V3052h)
                                                                                                      (!kl_V3052t))) -> pat_cond_1 kl_V3052 kl_V3052h kl_V3052t
                                                                                     _ -> pat_cond_3
                                                      _ -> throwError "if: expected boolean"

kl_explode :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_explode (!kl_V3054) = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                            !appl_1 <- kl_V3054 `pseq` applyWrapper aw_0 [kl_V3054,
                                                                          Core.Types.Atom (Core.Types.Str ""),
                                                                          Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                            appl_1 `pseq` kl_shen_explode_h appl_1

kl_shen_explode_h :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_explode_h (!kl_V3056) = do let pat_cond_0 = do return (Atom Nil)
                                       pat_cond_1 = do !kl_if_2 <- kl_V3056 `pseq` kl_shen_PlusstringP kl_V3056
                                                       case kl_if_2 of
                                                           Atom (B (True)) -> do !appl_3 <- kl_V3056 `pseq` pos kl_V3056 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                 !appl_4 <- kl_V3056 `pseq` tlstr kl_V3056
                                                                                 !appl_5 <- appl_4 `pseq` kl_shen_explode_h appl_4
                                                                                 appl_3 `pseq` (appl_5 `pseq` klCons appl_3 appl_5)
                                                           Atom (B (False)) -> do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                     applyWrapper aw_6 [ApplC (wrapNamed "shen.explode-h" kl_shen_explode_h)]
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V3056 of
                                           kl_V3056@(Atom (Str "")) -> pat_cond_0
                                           _ -> pat_cond_1

kl_cd :: Core.Types.KLValue ->
         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_cd (!kl_V3058) = do !appl_0 <- let pat_cond_1 = do return (Core.Types.Atom (Core.Types.Str ""))
                                      pat_cond_2 = do do let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                         kl_V3058 `pseq` applyWrapper aw_3 [kl_V3058,
                                                                                            Core.Types.Atom (Core.Types.Str "/"),
                                                                                            Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                   in case kl_V3058 of
                                          kl_V3058@(Atom (Str "")) -> pat_cond_1
                                          _ -> pat_cond_2
                       appl_0 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "*home-directory*")) appl_0

kl_for_each :: Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_for_each (!kl_V3061) (!kl_V3062) = do let !appl_0 = Atom Nil
                                         !kl_if_1 <- appl_0 `pseq` (kl_V3062 `pseq` eq appl_0 kl_V3062)
                                         case kl_if_1 of
                                             Atom (B (True)) -> do return (Atom (B True))
                                             Atom (B (False)) -> do let pat_cond_2 kl_V3062 kl_V3062h kl_V3062t = do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl__) -> do kl_V3061 `pseq` (kl_V3062t `pseq` kl_for_each kl_V3061 kl_V3062t))))
                                                                                                                     !appl_4 <- kl_V3062h `pseq` applyWrapper kl_V3061 [kl_V3062h]
                                                                                                                     appl_4 `pseq` applyWrapper appl_3 [appl_4]
                                                                        pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                           applyWrapper aw_6 [ApplC (wrapNamed "for-each" kl_for_each)]
                                                                     in case kl_V3062 of
                                                                            !(kl_V3062@(Cons (!kl_V3062h)
                                                                                             (!kl_V3062t))) -> pat_cond_2 kl_V3062 kl_V3062h kl_V3062t
                                                                            _ -> pat_cond_5
                                             _ -> throwError "if: expected boolean"

kl_fold_right :: Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_fold_right (!kl_V3066) (!kl_V3067) (!kl_V3068) = do let !appl_0 = Atom Nil
                                                       !kl_if_1 <- appl_0 `pseq` (kl_V3067 `pseq` eq appl_0 kl_V3067)
                                                       case kl_if_1 of
                                                           Atom (B (True)) -> do return kl_V3068
                                                           Atom (B (False)) -> do let pat_cond_2 kl_V3067 kl_V3067h kl_V3067t = do !appl_3 <- kl_V3066 `pseq` (kl_V3067t `pseq` (kl_V3068 `pseq` kl_fold_right kl_V3066 kl_V3067t kl_V3068))
                                                                                                                                   kl_V3067h `pseq` (appl_3 `pseq` applyWrapper kl_V3066 [kl_V3067h,
                                                                                                                                                                                          appl_3])
                                                                                      pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                         applyWrapper aw_5 [ApplC (wrapNamed "fold-right" kl_fold_right)]
                                                                                   in case kl_V3067 of
                                                                                          !(kl_V3067@(Cons (!kl_V3067h)
                                                                                                           (!kl_V3067t))) -> pat_cond_2 kl_V3067 kl_V3067h kl_V3067t
                                                                                          _ -> pat_cond_4
                                                           _ -> throwError "if: expected boolean"

kl_fold_left :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_fold_left (!kl_V3072) (!kl_V3073) (!kl_V3074) = do let !appl_0 = Atom Nil
                                                      !kl_if_1 <- appl_0 `pseq` (kl_V3074 `pseq` eq appl_0 kl_V3074)
                                                      case kl_if_1 of
                                                          Atom (B (True)) -> do return kl_V3073
                                                          Atom (B (False)) -> do let pat_cond_2 kl_V3074 kl_V3074h kl_V3074t = do !appl_3 <- kl_V3073 `pseq` (kl_V3074h `pseq` applyWrapper kl_V3072 [kl_V3073,
                                                                                                                                                                                                      kl_V3074h])
                                                                                                                                  kl_V3072 `pseq` (appl_3 `pseq` (kl_V3074t `pseq` kl_fold_left kl_V3072 appl_3 kl_V3074t))
                                                                                     pat_cond_4 = do do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                        applyWrapper aw_5 [ApplC (wrapNamed "fold-left" kl_fold_left)]
                                                                                  in case kl_V3074 of
                                                                                         !(kl_V3074@(Cons (!kl_V3074h)
                                                                                                          (!kl_V3074t))) -> pat_cond_2 kl_V3074 kl_V3074h kl_V3074t
                                                                                         _ -> pat_cond_4
                                                          _ -> throwError "if: expected boolean"

kl_filter :: Core.Types.KLValue ->
             Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_filter (!kl_V3077) (!kl_V3078) = do let !appl_0 = Atom Nil
                                       kl_V3077 `pseq` (appl_0 `pseq` (kl_V3078 `pseq` kl_shen_filter_h kl_V3077 appl_0 kl_V3078))

kl_shen_filter_h :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_filter_h (!kl_V3088) (!kl_V3089) (!kl_V3090) = do let !appl_0 = Atom Nil
                                                          !kl_if_1 <- appl_0 `pseq` (kl_V3090 `pseq` eq appl_0 kl_V3090)
                                                          case kl_if_1 of
                                                              Atom (B (True)) -> do kl_V3089 `pseq` kl_reverse kl_V3089
                                                              Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V3090 kl_V3090h kl_V3090t = do !kl_if_4 <- kl_V3090h `pseq` applyWrapper kl_V3088 [kl_V3090h]
                                                                                                                                                  case kl_if_4 of
                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                     pat_cond_5 = do do return (Atom (B False))
                                                                                                  in case kl_V3090 of
                                                                                                         !(kl_V3090@(Cons (!kl_V3090h)
                                                                                                                          (!kl_V3090t))) -> pat_cond_3 kl_V3090 kl_V3090h kl_V3090t
                                                                                                         _ -> pat_cond_5
                                                                                     case kl_if_2 of
                                                                                         Atom (B (True)) -> do !appl_6 <- kl_V3090 `pseq` hd kl_V3090
                                                                                                               !appl_7 <- appl_6 `pseq` (kl_V3089 `pseq` klCons appl_6 kl_V3089)
                                                                                                               !appl_8 <- kl_V3090 `pseq` tl kl_V3090
                                                                                                               kl_V3088 `pseq` (appl_7 `pseq` (appl_8 `pseq` kl_shen_filter_h kl_V3088 appl_7 appl_8))
                                                                                         Atom (B (False)) -> do let pat_cond_9 kl_V3090 kl_V3090h kl_V3090t = do kl_V3088 `pseq` (kl_V3089 `pseq` (kl_V3090t `pseq` kl_shen_filter_h kl_V3088 kl_V3089 kl_V3090t))
                                                                                                                    pat_cond_10 = do do let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                        applyWrapper aw_11 [ApplC (wrapNamed "shen.filter-h" kl_shen_filter_h)]
                                                                                                                 in case kl_V3090 of
                                                                                                                        !(kl_V3090@(Cons (!kl_V3090h)
                                                                                                                                         (!kl_V3090t))) -> pat_cond_9 kl_V3090 kl_V3090h kl_V3090t
                                                                                                                        _ -> pat_cond_10
                                                                                         _ -> throwError "if: expected boolean"
                                                              _ -> throwError "if: expected boolean"

kl_map :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_map (!kl_V3093) (!kl_V3094) = do let !appl_0 = Atom Nil
                                    kl_V3093 `pseq` (kl_V3094 `pseq` (appl_0 `pseq` kl_shen_map_h kl_V3093 kl_V3094 appl_0))

kl_shen_map_h :: Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_map_h (!kl_V3100) (!kl_V3101) (!kl_V3102) = do let !appl_0 = Atom Nil
                                                       !kl_if_1 <- appl_0 `pseq` (kl_V3101 `pseq` eq appl_0 kl_V3101)
                                                       case kl_if_1 of
                                                           Atom (B (True)) -> do kl_V3102 `pseq` kl_reverse kl_V3102
                                                           Atom (B (False)) -> do let pat_cond_2 kl_V3101 kl_V3101h kl_V3101t = do !appl_3 <- kl_V3101h `pseq` applyWrapper kl_V3100 [kl_V3101h]
                                                                                                                                   !appl_4 <- appl_3 `pseq` (kl_V3102 `pseq` klCons appl_3 kl_V3102)
                                                                                                                                   kl_V3100 `pseq` (kl_V3101t `pseq` (appl_4 `pseq` kl_shen_map_h kl_V3100 kl_V3101t appl_4))
                                                                                      pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                         applyWrapper aw_6 [ApplC (wrapNamed "shen.map-h" kl_shen_map_h)]
                                                                                   in case kl_V3101 of
                                                                                          !(kl_V3101@(Cons (!kl_V3101h)
                                                                                                           (!kl_V3101t))) -> pat_cond_2 kl_V3101 kl_V3101h kl_V3101t
                                                                                          _ -> pat_cond_5
                                                           _ -> throwError "if: expected boolean"

kl_length :: Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_length (!kl_V3104) = do kl_V3104 `pseq` kl_shen_length_h kl_V3104 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))

kl_shen_length_h :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_length_h (!kl_V3107) (!kl_V3108) = do let !appl_0 = Atom Nil
                                              !kl_if_1 <- appl_0 `pseq` (kl_V3107 `pseq` eq appl_0 kl_V3107)
                                              case kl_if_1 of
                                                  Atom (B (True)) -> do return kl_V3108
                                                  Atom (B (False)) -> do do !appl_2 <- kl_V3107 `pseq` tl kl_V3107
                                                                            !appl_3 <- kl_V3108 `pseq` add kl_V3108 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                            appl_2 `pseq` (appl_3 `pseq` kl_shen_length_h appl_2 appl_3)
                                                  _ -> throwError "if: expected boolean"

kl_occurrences :: Core.Types.KLValue ->
                  Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_occurrences (!kl_V3120) (!kl_V3121) = do !kl_if_0 <- kl_V3121 `pseq` (kl_V3120 `pseq` eq kl_V3121 kl_V3120)
                                            case kl_if_0 of
                                                Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                Atom (B (False)) -> do let pat_cond_1 kl_V3121 kl_V3121h kl_V3121t = do !appl_2 <- kl_V3120 `pseq` (kl_V3121h `pseq` kl_occurrences kl_V3120 kl_V3121h)
                                                                                                                        !appl_3 <- kl_V3120 `pseq` (kl_V3121t `pseq` kl_occurrences kl_V3120 kl_V3121t)
                                                                                                                        appl_2 `pseq` (appl_3 `pseq` add appl_2 appl_3)
                                                                           pat_cond_4 = do do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                        in case kl_V3121 of
                                                                               !(kl_V3121@(Cons (!kl_V3121h)
                                                                                                (!kl_V3121t))) -> pat_cond_1 kl_V3121 kl_V3121h kl_V3121t
                                                                               _ -> pat_cond_4
                                                _ -> throwError "if: expected boolean"

kl_nth :: Core.Types.KLValue ->
          Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_nth (!kl_V3130) (!kl_V3131) = do !kl_if_0 <- let pat_cond_1 = do let pat_cond_2 kl_V3131 kl_V3131h kl_V3131t = do return (Atom (B True))
                                                                        pat_cond_3 = do do return (Atom (B False))
                                                                     in case kl_V3131 of
                                                                            !(kl_V3131@(Cons (!kl_V3131h)
                                                                                             (!kl_V3131t))) -> pat_cond_2 kl_V3131 kl_V3131h kl_V3131t
                                                                            _ -> pat_cond_3
                                                    pat_cond_4 = do do return (Atom (B False))
                                                 in case kl_V3130 of
                                                        kl_V3130@(Atom (N (KI 1))) -> pat_cond_1
                                                        _ -> pat_cond_4
                                    case kl_if_0 of
                                        Atom (B (True)) -> do kl_V3131 `pseq` hd kl_V3131
                                        Atom (B (False)) -> do let pat_cond_5 kl_V3131 kl_V3131h kl_V3131t = do !appl_6 <- kl_V3130 `pseq` Primitives.subtract kl_V3130 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                appl_6 `pseq` (kl_V3131t `pseq` kl_nth appl_6 kl_V3131t)
                                                                   pat_cond_7 = do do let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                      applyWrapper aw_8 [ApplC (wrapNamed "nth" kl_nth)]
                                                                in case kl_V3131 of
                                                                       !(kl_V3131@(Cons (!kl_V3131h)
                                                                                        (!kl_V3131t))) -> pat_cond_5 kl_V3131 kl_V3131h kl_V3131t
                                                                       _ -> pat_cond_7
                                        _ -> throwError "if: expected boolean"

kl_integerP :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_integerP (Atom (N (KI _))) = return (Atom (B True))
kl_integerP (Atom (N (KD d))) = return (Atom (B (fromInteger (round d) == d)))
kl_integerP !v = return (Atom (B False))

kl_shen_abs :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_abs (!kl_V3135) = do !kl_if_0 <- kl_V3135 `pseq` greaterThan kl_V3135 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                             case kl_if_0 of
                                 Atom (B (True)) -> do return kl_V3135
                                 Atom (B (False)) -> do do kl_V3135 `pseq` Primitives.subtract (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) kl_V3135
                                 _ -> throwError "if: expected boolean"

kl_shen_magless :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_magless (!kl_V3138) (!kl_V3139) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Nx2) -> do !kl_if_1 <- kl_Nx2 `pseq` (kl_V3138 `pseq` greaterThan kl_Nx2 kl_V3138)
                                                                                                           case kl_if_1 of
                                                                                                               Atom (B (True)) -> do return kl_V3139
                                                                                                               Atom (B (False)) -> do do kl_V3138 `pseq` (kl_Nx2 `pseq` kl_shen_magless kl_V3138 kl_Nx2)
                                                                                                               _ -> throwError "if: expected boolean")))
                                             !appl_2 <- kl_V3139 `pseq` multiply kl_V3139 (Core.Types.Atom (Core.Types.N (Core.Types.KI 2)))
                                             appl_2 `pseq` applyWrapper appl_0 [appl_2]

kl_shen_integer_testP :: Core.Types.KLValue ->
                         Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_integer_testP (!kl_V3145) (!kl_V3146) = do let pat_cond_0 = do return (Atom (B True))
                                                       pat_cond_1 = do !kl_if_2 <- kl_V3145 `pseq` greaterThan (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V3145
                                                                       case kl_if_2 of
                                                                           Atom (B (True)) -> do return (Atom (B False))
                                                                           Atom (B (False)) -> do do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Abs_N) -> do !kl_if_4 <- kl_Abs_N `pseq` greaterThan (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) kl_Abs_N
                                                                                                                                                                     case kl_if_4 of
                                                                                                                                                                         Atom (B (True)) -> do kl_V3145 `pseq` kl_integerP kl_V3145
                                                                                                                                                                         Atom (B (False)) -> do do kl_Abs_N `pseq` (kl_V3146 `pseq` kl_shen_integer_testP kl_Abs_N kl_V3146)
                                                                                                                                                                         _ -> throwError "if: expected boolean")))
                                                                                                     !appl_5 <- kl_V3145 `pseq` (kl_V3146 `pseq` Primitives.subtract kl_V3145 kl_V3146)
                                                                                                     appl_5 `pseq` applyWrapper appl_3 [appl_5]
                                                                           _ -> throwError "if: expected boolean"
                                                    in case kl_V3145 of
                                                           kl_V3145@(Atom (N (KI 0))) -> pat_cond_0
                                                           _ -> pat_cond_1

kl_mapcan :: Core.Types.KLValue ->
             Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_mapcan (!kl_V3151) (!kl_V3152) = do let !appl_0 = Atom Nil
                                       !kl_if_1 <- appl_0 `pseq` (kl_V3152 `pseq` eq appl_0 kl_V3152)
                                       case kl_if_1 of
                                           Atom (B (True)) -> do return (Atom Nil)
                                           Atom (B (False)) -> do let pat_cond_2 kl_V3152 kl_V3152h kl_V3152t = do !appl_3 <- kl_V3152h `pseq` applyWrapper kl_V3151 [kl_V3152h]
                                                                                                                   !appl_4 <- kl_V3151 `pseq` (kl_V3152t `pseq` kl_mapcan kl_V3151 kl_V3152t)
                                                                                                                   appl_3 `pseq` (appl_4 `pseq` kl_append appl_3 appl_4)
                                                                      pat_cond_5 = do do let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                         applyWrapper aw_6 [ApplC (wrapNamed "mapcan" kl_mapcan)]
                                                                   in case kl_V3152 of
                                                                          !(kl_V3152@(Cons (!kl_V3152h)
                                                                                           (!kl_V3152t))) -> pat_cond_2 kl_V3152 kl_V3152h kl_V3152t
                                                                          _ -> pat_cond_5
                                           _ -> throwError "if: expected boolean"

kl_EqEq :: Core.Types.KLValue ->
           Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_EqEq (!kl_V3164) (!kl_V3165) = do !kl_if_0 <- kl_V3165 `pseq` (kl_V3164 `pseq` eq kl_V3165 kl_V3164)
                                     case kl_if_0 of
                                         Atom (B (True)) -> do return (Atom (B True))
                                         Atom (B (False)) -> do do return (Atom (B False))
                                         _ -> throwError "if: expected boolean"

kl_abort :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_abort = do simpleError (Core.Types.Atom (Core.Types.Str ""))

kl_boundP :: Core.Types.KLValue ->
             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_boundP (!kl_V3167) = do !kl_if_0 <- kl_V3167 `pseq` kl_symbolP kl_V3167
                           case kl_if_0 of
                               Atom (B (True)) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Val) -> do let pat_cond_2 = do return (Atom (B False))
                                                                                                                       pat_cond_3 = do do return (Atom (B True))
                                                                                                                    in case kl_Val of
                                                                                                                           kl_Val@(Atom (UnboundSym "shen.this-symbol-is-unbound")) -> pat_cond_2
                                                                                                                           kl_Val@(ApplC (PL "shen.this-symbol-is-unbound"
                                                                                                                                             _)) -> pat_cond_2
                                                                                                                           kl_Val@(ApplC (Func "shen.this-symbol-is-unbound"
                                                                                                                                               _)) -> pat_cond_2
                                                                                                                           _ -> pat_cond_3)))
                                                     let !appl_4 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.UnboundSym "shen.this-symbol-is-unbound"))))
                                                     !appl_5 <- kl_V3167 `pseq` (appl_4 `pseq` kl_valueDivor kl_V3167 appl_4)
                                                     !kl_if_6 <- appl_5 `pseq` applyWrapper appl_1 [appl_5]
                                                     case kl_if_6 of
                                                         Atom (B (True)) -> do return (Atom (B True))
                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                         _ -> throwError "if: expected boolean"
                               Atom (B (False)) -> do do return (Atom (B False))
                               _ -> throwError "if: expected boolean"

kl_shen_string_RBbytes :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_string_RBbytes (!kl_V3169) = do let pat_cond_0 = do return (Atom Nil)
                                            pat_cond_1 = do do !appl_2 <- kl_V3169 `pseq` pos kl_V3169 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                               !appl_3 <- appl_2 `pseq` stringToN appl_2
                                                               !appl_4 <- kl_V3169 `pseq` tlstr kl_V3169
                                                               !appl_5 <- appl_4 `pseq` kl_shen_string_RBbytes appl_4
                                                               appl_3 `pseq` (appl_5 `pseq` klCons appl_3 appl_5)
                                         in case kl_V3169 of
                                                kl_V3169@(Atom (Str "")) -> pat_cond_0
                                                _ -> pat_cond_1

kl_maxinferences :: Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_maxinferences (!kl_V3171) = do kl_V3171 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*maxinferences*")) kl_V3171

kl_inferences :: Core.Types.KLContext Core.Types.Env
                                      Core.Types.KLValue
kl_inferences = do value (Core.Types.Atom (Core.Types.UnboundSym "shen.*infs*"))

kl_protect :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_protect (!kl_V3173) = do return kl_V3173

kl_stoutput :: Core.Types.KLContext Core.Types.Env
                                    Core.Types.KLValue
kl_stoutput = do value (Core.Types.Atom (Core.Types.UnboundSym "*stoutput*"))

kl_sterror :: Core.Types.KLContext Core.Types.Env
                                   Core.Types.KLValue
kl_sterror = do value (Core.Types.Atom (Core.Types.UnboundSym "shen.*sterror*"))

kl_string_RBsymbol :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_string_RBsymbol (!kl_V3175) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Symbol) -> do !kl_if_1 <- kl_Symbol `pseq` kl_symbolP kl_Symbol
                                                                                                     case kl_if_1 of
                                                                                                         Atom (B (True)) -> do return kl_Symbol
                                                                                                         Atom (B (False)) -> do do let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                   !appl_3 <- kl_V3175 `pseq` applyWrapper aw_2 [kl_V3175,
                                                                                                                                                                                 Core.Types.Atom (Core.Types.Str " to a symbol"),
                                                                                                                                                                                 Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                                                                                                   !appl_4 <- appl_3 `pseq` cn (Core.Types.Atom (Core.Types.Str "cannot intern ")) appl_3
                                                                                                                                   appl_4 `pseq` simpleError appl_4
                                                                                                         _ -> throwError "if: expected boolean")))
                                    !appl_5 <- kl_V3175 `pseq` intern kl_V3175
                                    appl_5 `pseq` applyWrapper appl_0 [appl_5]

kl_optimise :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_optimise (!kl_V3181) = do let pat_cond_0 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*optimise*")) (Atom (B True))
                                 pat_cond_1 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*optimise*")) (Atom (B False))
                                 pat_cond_2 = do do simpleError (Core.Types.Atom (Core.Types.Str "optimise expects a + or a -.\n"))
                              in case kl_V3181 of
                                     kl_V3181@(Atom (UnboundSym "+")) -> pat_cond_0
                                     kl_V3181@(ApplC (PL "+" _)) -> pat_cond_0
                                     kl_V3181@(ApplC (Func "+" _)) -> pat_cond_0
                                     kl_V3181@(Atom (UnboundSym "-")) -> pat_cond_1
                                     kl_V3181@(ApplC (PL "-" _)) -> pat_cond_1
                                     kl_V3181@(ApplC (Func "-" _)) -> pat_cond_1
                                     _ -> pat_cond_2

kl_os :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_os = do value (Core.Types.Atom (Core.Types.UnboundSym "*os*"))

kl_language :: Core.Types.KLContext Core.Types.Env
                                    Core.Types.KLValue
kl_language = do value (Core.Types.Atom (Core.Types.UnboundSym "*language*"))

kl_version :: Core.Types.KLContext Core.Types.Env
                                   Core.Types.KLValue
kl_version = do value (Core.Types.Atom (Core.Types.UnboundSym "*version*"))

kl_port :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_port = do value (Core.Types.Atom (Core.Types.UnboundSym "*port*"))

kl_porters :: Core.Types.KLContext Core.Types.Env
                                   Core.Types.KLValue
kl_porters = do value (Core.Types.Atom (Core.Types.UnboundSym "*porters*"))

kl_implementation :: Core.Types.KLContext Core.Types.Env
                                          Core.Types.KLValue
kl_implementation = do value (Core.Types.Atom (Core.Types.UnboundSym "*implementation*"))

kl_release :: Core.Types.KLContext Core.Types.Env
                                   Core.Types.KLValue
kl_release = do value (Core.Types.Atom (Core.Types.UnboundSym "*release*"))

kl_packageP :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_packageP (!kl_V3183) = do (do !appl_0 <- kl_V3183 `pseq` kl_external kl_V3183
                                 appl_0 `pseq` kl_do appl_0 (Atom (B True))) `catchError` (\(!kl_E) -> do return (Atom (B False)))

kl_function :: Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_function (!kl_V3185) = do kl_V3185 `pseq` kl_shen_lookup_func kl_V3185

kl_shen_lookup_func :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_lookup_func (!kl_V3187) = do let !appl_0 = ApplC (PL "thunk" (do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                         !appl_2 <- kl_V3187 `pseq` applyWrapper aw_1 [kl_V3187,
                                                                                                                       Core.Types.Atom (Core.Types.Str " has no lambda expansion\n"),
                                                                                                                       Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                         appl_2 `pseq` simpleError appl_2))
                                     !appl_3 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                     kl_V3187 `pseq` (appl_0 `pseq` (appl_3 `pseq` kl_getDivor kl_V3187 (Core.Types.Atom (Core.Types.UnboundSym "shen.lambda-form")) appl_0 appl_3))

expr2 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr2 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
