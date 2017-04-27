{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Macros where

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

kl_macroexpand :: Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_macroexpand (!kl_V1529) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do !kl_if_1 <- kl_V1529 `pseq` (kl_Y `pseq` eq kl_V1529 kl_Y)
                                                                                            case kl_if_1 of
                                                                                                Atom (B (True)) -> do return kl_V1529
                                                                                                Atom (B (False)) -> do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_macroexpand kl_Z)))
                                                                                                                          appl_2 `pseq` (kl_Y `pseq` kl_shen_walk appl_2 kl_Y)
                                                                                                _ -> throwError "if: expected boolean")))
                                !appl_3 <- value (Core.Types.Atom (Core.Types.UnboundSym "*macros*"))
                                !appl_4 <- appl_3 `pseq` (kl_V1529 `pseq` kl_shen_compose appl_3 kl_V1529)
                                appl_4 `pseq` applyWrapper appl_0 [appl_4]

kl_shen_error_macro :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_error_macro (!kl_V1531) = do let pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt = do !appl_1 <- kl_V1531th `pseq` (kl_V1531tt `pseq` kl_shen_mkstr kl_V1531th kl_V1531tt)
                                                                                                  let !appl_2 = Atom Nil
                                                                                                  !appl_3 <- appl_1 `pseq` (appl_2 `pseq` klCons appl_1 appl_2)
                                                                                                  appl_3 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_3
                                         pat_cond_4 = do do return kl_V1531
                                      in case kl_V1531 of
                                             !(kl_V1531@(Cons (Atom (UnboundSym "error"))
                                                              (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                 (!kl_V1531tt)))))) -> pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt
                                             !(kl_V1531@(Cons (ApplC (PL "error" _))
                                                              (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                 (!kl_V1531tt)))))) -> pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt
                                             !(kl_V1531@(Cons (ApplC (Func "error" _))
                                                              (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                 (!kl_V1531tt)))))) -> pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt
                                             _ -> pat_cond_4

kl_shen_output_macro :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_output_macro (!kl_V1533) = do let pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt = do !appl_1 <- kl_V1533th `pseq` (kl_V1533tt `pseq` kl_shen_mkstr kl_V1533th kl_V1533tt)
                                                                                                   let !appl_2 = Atom Nil
                                                                                                   !appl_3 <- appl_2 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_2
                                                                                                   let !appl_4 = Atom Nil
                                                                                                   !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                   !appl_6 <- appl_1 `pseq` (appl_5 `pseq` klCons appl_1 appl_5)
                                                                                                   appl_6 `pseq` klCons (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_6
                                          pat_cond_7 = do !kl_if_8 <- let pat_cond_9 kl_V1533 kl_V1533h kl_V1533t = do !kl_if_10 <- let pat_cond_11 = do !kl_if_12 <- let pat_cond_13 kl_V1533t kl_V1533th kl_V1533tt = do let !appl_14 = Atom Nil
                                                                                                                                                                                                                           !kl_if_15 <- appl_14 `pseq` (kl_V1533tt `pseq` eq appl_14 kl_V1533tt)
                                                                                                                                                                                                                           case kl_if_15 of
                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                          pat_cond_16 = do do return (Atom (B False))
                                                                                                                                                                       in case kl_V1533t of
                                                                                                                                                                              !(kl_V1533t@(Cons (!kl_V1533th)
                                                                                                                                                                                                (!kl_V1533tt))) -> pat_cond_13 kl_V1533t kl_V1533th kl_V1533tt
                                                                                                                                                                              _ -> pat_cond_16
                                                                                                                                                         case kl_if_12 of
                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                        pat_cond_17 = do do return (Atom (B False))
                                                                                                                                     in case kl_V1533h of
                                                                                                                                            kl_V1533h@(Atom (UnboundSym "pr")) -> pat_cond_11
                                                                                                                                            kl_V1533h@(ApplC (PL "pr"
                                                                                                                                                                 _)) -> pat_cond_11
                                                                                                                                            kl_V1533h@(ApplC (Func "pr"
                                                                                                                                                                   _)) -> pat_cond_11
                                                                                                                                            _ -> pat_cond_17
                                                                                                                       case kl_if_10 of
                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                           _ -> throwError "if: expected boolean"
                                                                          pat_cond_18 = do do return (Atom (B False))
                                                                       in case kl_V1533 of
                                                                              !(kl_V1533@(Cons (!kl_V1533h)
                                                                                               (!kl_V1533t))) -> pat_cond_9 kl_V1533 kl_V1533h kl_V1533t
                                                                              _ -> pat_cond_18
                                                          case kl_if_8 of
                                                              Atom (B (True)) -> do !appl_19 <- kl_V1533 `pseq` tl kl_V1533
                                                                                    !appl_20 <- appl_19 `pseq` hd appl_19
                                                                                    let !appl_21 = Atom Nil
                                                                                    !appl_22 <- appl_21 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_21
                                                                                    let !appl_23 = Atom Nil
                                                                                    !appl_24 <- appl_22 `pseq` (appl_23 `pseq` klCons appl_22 appl_23)
                                                                                    !appl_25 <- appl_20 `pseq` (appl_24 `pseq` klCons appl_20 appl_24)
                                                                                    appl_25 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_25
                                                              Atom (B (False)) -> do do return kl_V1533
                                                              _ -> throwError "if: expected boolean"
                                       in case kl_V1533 of
                                              !(kl_V1533@(Cons (Atom (UnboundSym "output"))
                                                               (!(kl_V1533t@(Cons (!kl_V1533th)
                                                                                  (!kl_V1533tt)))))) -> pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt
                                              !(kl_V1533@(Cons (ApplC (PL "output" _))
                                                               (!(kl_V1533t@(Cons (!kl_V1533th)
                                                                                  (!kl_V1533tt)))))) -> pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt
                                              !(kl_V1533@(Cons (ApplC (Func "output" _))
                                                               (!(kl_V1533t@(Cons (!kl_V1533th)
                                                                                  (!kl_V1533tt)))))) -> pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt
                                              _ -> pat_cond_7

kl_shen_make_string_macro :: Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_make_string_macro (!kl_V1535) = do let pat_cond_0 kl_V1535 kl_V1535t kl_V1535th kl_V1535tt = do kl_V1535th `pseq` (kl_V1535tt `pseq` kl_shen_mkstr kl_V1535th kl_V1535tt)
                                               pat_cond_1 = do do return kl_V1535
                                            in case kl_V1535 of
                                                   !(kl_V1535@(Cons (Atom (UnboundSym "make-string"))
                                                                    (!(kl_V1535t@(Cons (!kl_V1535th)
                                                                                       (!kl_V1535tt)))))) -> pat_cond_0 kl_V1535 kl_V1535t kl_V1535th kl_V1535tt
                                                   !(kl_V1535@(Cons (ApplC (PL "make-string" _))
                                                                    (!(kl_V1535t@(Cons (!kl_V1535th)
                                                                                       (!kl_V1535tt)))))) -> pat_cond_0 kl_V1535 kl_V1535t kl_V1535th kl_V1535tt
                                                   !(kl_V1535@(Cons (ApplC (Func "make-string" _))
                                                                    (!(kl_V1535t@(Cons (!kl_V1535th)
                                                                                       (!kl_V1535tt)))))) -> pat_cond_0 kl_V1535 kl_V1535t kl_V1535th kl_V1535tt
                                                   _ -> pat_cond_1

kl_shen_input_macro :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_input_macro (!kl_V1537) = do !kl_if_0 <- let pat_cond_1 kl_V1537 kl_V1537h kl_V1537t = do !kl_if_2 <- let pat_cond_3 = do let !appl_4 = Atom Nil
                                                                                                                                  !kl_if_5 <- appl_4 `pseq` (kl_V1537t `pseq` eq appl_4 kl_V1537t)
                                                                                                                                  case kl_if_5 of
                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                  pat_cond_6 = do do return (Atom (B False))
                                                                                                               in case kl_V1537h of
                                                                                                                      kl_V1537h@(Atom (UnboundSym "lineread")) -> pat_cond_3
                                                                                                                      kl_V1537h@(ApplC (PL "lineread"
                                                                                                                                           _)) -> pat_cond_3
                                                                                                                      kl_V1537h@(ApplC (Func "lineread"
                                                                                                                                             _)) -> pat_cond_3
                                                                                                                      _ -> pat_cond_6
                                                                                                  case kl_if_2 of
                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                      _ -> throwError "if: expected boolean"
                                                     pat_cond_7 = do do return (Atom (B False))
                                                  in case kl_V1537 of
                                                         !(kl_V1537@(Cons (!kl_V1537h)
                                                                          (!kl_V1537t))) -> pat_cond_1 kl_V1537 kl_V1537h kl_V1537t
                                                         _ -> pat_cond_7
                                     case kl_if_0 of
                                         Atom (B (True)) -> do let !appl_8 = Atom Nil
                                                               !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_8
                                                               let !appl_10 = Atom Nil
                                                               !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                               appl_11 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_11
                                         Atom (B (False)) -> do !kl_if_12 <- let pat_cond_13 kl_V1537 kl_V1537h kl_V1537t = do !kl_if_14 <- let pat_cond_15 = do let !appl_16 = Atom Nil
                                                                                                                                                                 !kl_if_17 <- appl_16 `pseq` (kl_V1537t `pseq` eq appl_16 kl_V1537t)
                                                                                                                                                                 case kl_if_17 of
                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                pat_cond_18 = do do return (Atom (B False))
                                                                                                                                             in case kl_V1537h of
                                                                                                                                                    kl_V1537h@(Atom (UnboundSym "input")) -> pat_cond_15
                                                                                                                                                    kl_V1537h@(ApplC (PL "input"
                                                                                                                                                                         _)) -> pat_cond_15
                                                                                                                                                    kl_V1537h@(ApplC (Func "input"
                                                                                                                                                                           _)) -> pat_cond_15
                                                                                                                                                    _ -> pat_cond_18
                                                                                                                               case kl_if_14 of
                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                 pat_cond_19 = do do return (Atom (B False))
                                                                              in case kl_V1537 of
                                                                                     !(kl_V1537@(Cons (!kl_V1537h)
                                                                                                      (!kl_V1537t))) -> pat_cond_13 kl_V1537 kl_V1537h kl_V1537t
                                                                                     _ -> pat_cond_19
                                                                case kl_if_12 of
                                                                    Atom (B (True)) -> do let !appl_20 = Atom Nil
                                                                                          !appl_21 <- appl_20 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_20
                                                                                          let !appl_22 = Atom Nil
                                                                                          !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                                                                                          appl_23 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_23
                                                                    Atom (B (False)) -> do !kl_if_24 <- let pat_cond_25 kl_V1537 kl_V1537h kl_V1537t = do !kl_if_26 <- let pat_cond_27 = do let !appl_28 = Atom Nil
                                                                                                                                                                                            !kl_if_29 <- appl_28 `pseq` (kl_V1537t `pseq` eq appl_28 kl_V1537t)
                                                                                                                                                                                            case kl_if_29 of
                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                           pat_cond_30 = do do return (Atom (B False))
                                                                                                                                                                        in case kl_V1537h of
                                                                                                                                                                               kl_V1537h@(Atom (UnboundSym "read")) -> pat_cond_27
                                                                                                                                                                               kl_V1537h@(ApplC (PL "read"
                                                                                                                                                                                                    _)) -> pat_cond_27
                                                                                                                                                                               kl_V1537h@(ApplC (Func "read"
                                                                                                                                                                                                      _)) -> pat_cond_27
                                                                                                                                                                               _ -> pat_cond_30
                                                                                                                                                          case kl_if_26 of
                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                            pat_cond_31 = do do return (Atom (B False))
                                                                                                         in case kl_V1537 of
                                                                                                                !(kl_V1537@(Cons (!kl_V1537h)
                                                                                                                                 (!kl_V1537t))) -> pat_cond_25 kl_V1537 kl_V1537h kl_V1537t
                                                                                                                _ -> pat_cond_31
                                                                                           case kl_if_24 of
                                                                                               Atom (B (True)) -> do let !appl_32 = Atom Nil
                                                                                                                     !appl_33 <- appl_32 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_32
                                                                                                                     let !appl_34 = Atom Nil
                                                                                                                     !appl_35 <- appl_33 `pseq` (appl_34 `pseq` klCons appl_33 appl_34)
                                                                                                                     appl_35 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_35
                                                                                               Atom (B (False)) -> do !kl_if_36 <- let pat_cond_37 kl_V1537 kl_V1537h kl_V1537t = do !kl_if_38 <- let pat_cond_39 = do !kl_if_40 <- let pat_cond_41 kl_V1537t kl_V1537th kl_V1537tt = do let !appl_42 = Atom Nil
                                                                                                                                                                                                                                                                                         !kl_if_43 <- appl_42 `pseq` (kl_V1537tt `pseq` eq appl_42 kl_V1537tt)
                                                                                                                                                                                                                                                                                         case kl_if_43 of
                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                        pat_cond_44 = do do return (Atom (B False))
                                                                                                                                                                                                                                     in case kl_V1537t of
                                                                                                                                                                                                                                            !(kl_V1537t@(Cons (!kl_V1537th)
                                                                                                                                                                                                                                                              (!kl_V1537tt))) -> pat_cond_41 kl_V1537t kl_V1537th kl_V1537tt
                                                                                                                                                                                                                                            _ -> pat_cond_44
                                                                                                                                                                                                                       case kl_if_40 of
                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                      pat_cond_45 = do do return (Atom (B False))
                                                                                                                                                                                                   in case kl_V1537h of
                                                                                                                                                                                                          kl_V1537h@(Atom (UnboundSym "input+")) -> pat_cond_39
                                                                                                                                                                                                          kl_V1537h@(ApplC (PL "input+"
                                                                                                                                                                                                                               _)) -> pat_cond_39
                                                                                                                                                                                                          kl_V1537h@(ApplC (Func "input+"
                                                                                                                                                                                                                                 _)) -> pat_cond_39
                                                                                                                                                                                                          _ -> pat_cond_45
                                                                                                                                                                                     case kl_if_38 of
                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                       pat_cond_46 = do do return (Atom (B False))
                                                                                                                                    in case kl_V1537 of
                                                                                                                                           !(kl_V1537@(Cons (!kl_V1537h)
                                                                                                                                                            (!kl_V1537t))) -> pat_cond_37 kl_V1537 kl_V1537h kl_V1537t
                                                                                                                                           _ -> pat_cond_46
                                                                                                                      case kl_if_36 of
                                                                                                                          Atom (B (True)) -> do !appl_47 <- kl_V1537 `pseq` tl kl_V1537
                                                                                                                                                !appl_48 <- appl_47 `pseq` hd appl_47
                                                                                                                                                let !appl_49 = Atom Nil
                                                                                                                                                !appl_50 <- appl_49 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_49
                                                                                                                                                let !appl_51 = Atom Nil
                                                                                                                                                !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                                                                                                                                                !appl_53 <- appl_48 `pseq` (appl_52 `pseq` klCons appl_48 appl_52)
                                                                                                                                                appl_53 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_53
                                                                                                                          Atom (B (False)) -> do !kl_if_54 <- let pat_cond_55 kl_V1537 kl_V1537h kl_V1537t = do !kl_if_56 <- let pat_cond_57 = do let !appl_58 = Atom Nil
                                                                                                                                                                                                                                                  !kl_if_59 <- appl_58 `pseq` (kl_V1537t `pseq` eq appl_58 kl_V1537t)
                                                                                                                                                                                                                                                  case kl_if_59 of
                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                 pat_cond_60 = do do return (Atom (B False))
                                                                                                                                                                                                                              in case kl_V1537h of
                                                                                                                                                                                                                                     kl_V1537h@(Atom (UnboundSym "read-byte")) -> pat_cond_57
                                                                                                                                                                                                                                     kl_V1537h@(ApplC (PL "read-byte"
                                                                                                                                                                                                                                                          _)) -> pat_cond_57
                                                                                                                                                                                                                                     kl_V1537h@(ApplC (Func "read-byte"
                                                                                                                                                                                                                                                            _)) -> pat_cond_57
                                                                                                                                                                                                                                     _ -> pat_cond_60
                                                                                                                                                                                                                case kl_if_56 of
                                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                  pat_cond_61 = do do return (Atom (B False))
                                                                                                                                                               in case kl_V1537 of
                                                                                                                                                                      !(kl_V1537@(Cons (!kl_V1537h)
                                                                                                                                                                                       (!kl_V1537t))) -> pat_cond_55 kl_V1537 kl_V1537h kl_V1537t
                                                                                                                                                                      _ -> pat_cond_61
                                                                                                                                                 case kl_if_54 of
                                                                                                                                                     Atom (B (True)) -> do let !appl_62 = Atom Nil
                                                                                                                                                                           !appl_63 <- appl_62 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_62
                                                                                                                                                                           let !appl_64 = Atom Nil
                                                                                                                                                                           !appl_65 <- appl_63 `pseq` (appl_64 `pseq` klCons appl_63 appl_64)
                                                                                                                                                                           appl_65 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_65
                                                                                                                                                     Atom (B (False)) -> do !kl_if_66 <- let pat_cond_67 kl_V1537 kl_V1537h kl_V1537t = do !kl_if_68 <- let pat_cond_69 = do let !appl_70 = Atom Nil
                                                                                                                                                                                                                                                                             !kl_if_71 <- appl_70 `pseq` (kl_V1537t `pseq` eq appl_70 kl_V1537t)
                                                                                                                                                                                                                                                                             case kl_if_71 of
                                                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                            pat_cond_72 = do do return (Atom (B False))
                                                                                                                                                                                                                                                         in case kl_V1537h of
                                                                                                                                                                                                                                                                kl_V1537h@(Atom (UnboundSym "read-char-code")) -> pat_cond_69
                                                                                                                                                                                                                                                                kl_V1537h@(ApplC (PL "read-char-code"
                                                                                                                                                                                                                                                                                     _)) -> pat_cond_69
                                                                                                                                                                                                                                                                kl_V1537h@(ApplC (Func "read-char-code"
                                                                                                                                                                                                                                                                                       _)) -> pat_cond_69
                                                                                                                                                                                                                                                                _ -> pat_cond_72
                                                                                                                                                                                                                                           case kl_if_68 of
                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                             pat_cond_73 = do do return (Atom (B False))
                                                                                                                                                                                          in case kl_V1537 of
                                                                                                                                                                                                 !(kl_V1537@(Cons (!kl_V1537h)
                                                                                                                                                                                                                  (!kl_V1537t))) -> pat_cond_67 kl_V1537 kl_V1537h kl_V1537t
                                                                                                                                                                                                 _ -> pat_cond_73
                                                                                                                                                                            case kl_if_66 of
                                                                                                                                                                                Atom (B (True)) -> do let !appl_74 = Atom Nil
                                                                                                                                                                                                      !appl_75 <- appl_74 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_74
                                                                                                                                                                                                      let !appl_76 = Atom Nil
                                                                                                                                                                                                      !appl_77 <- appl_75 `pseq` (appl_76 `pseq` klCons appl_75 appl_76)
                                                                                                                                                                                                      appl_77 `pseq` klCons (ApplC (wrapNamed "read-char-code" kl_read_char_code)) appl_77
                                                                                                                                                                                Atom (B (False)) -> do do return kl_V1537
                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                               _ -> throwError "if: expected boolean"
                                                                    _ -> throwError "if: expected boolean"
                                         _ -> throwError "if: expected boolean"

kl_shen_compose :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_compose (!kl_V1540) (!kl_V1541) = do let !appl_0 = Atom Nil
                                             !kl_if_1 <- appl_0 `pseq` (kl_V1540 `pseq` eq appl_0 kl_V1540)
                                             case kl_if_1 of
                                                 Atom (B (True)) -> do return kl_V1541
                                                 Atom (B (False)) -> do let pat_cond_2 kl_V1540 kl_V1540h kl_V1540t = do !appl_3 <- kl_V1541 `pseq` applyWrapper kl_V1540h [kl_V1541]
                                                                                                                         kl_V1540t `pseq` (appl_3 `pseq` kl_shen_compose kl_V1540t appl_3)
                                                                            pat_cond_4 = do do kl_shen_f_error (ApplC (wrapNamed "shen.compose" kl_shen_compose))
                                                                         in case kl_V1540 of
                                                                                !(kl_V1540@(Cons (!kl_V1540h)
                                                                                                 (!kl_V1540t))) -> pat_cond_2 kl_V1540 kl_V1540h kl_V1540t
                                                                                _ -> pat_cond_4
                                                 _ -> throwError "if: expected boolean"

kl_shen_compile_macro :: Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_compile_macro (!kl_V1543) = do !kl_if_0 <- let pat_cond_1 kl_V1543 kl_V1543h kl_V1543t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V1543t kl_V1543th kl_V1543tt = do !kl_if_6 <- let pat_cond_7 kl_V1543tt kl_V1543tth kl_V1543ttt = do let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                       !kl_if_9 <- appl_8 `pseq` (kl_V1543ttt `pseq` eq appl_8 kl_V1543ttt)
                                                                                                                                                                                                                                                                       case kl_if_9 of
                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                    pat_cond_10 = do do return (Atom (B False))
                                                                                                                                                                                                                 in case kl_V1543tt of
                                                                                                                                                                                                                        !(kl_V1543tt@(Cons (!kl_V1543tth)
                                                                                                                                                                                                                                           (!kl_V1543ttt))) -> pat_cond_7 kl_V1543tt kl_V1543tth kl_V1543ttt
                                                                                                                                                                                                                        _ -> pat_cond_10
                                                                                                                                                                                                    case kl_if_6 of
                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                    pat_cond_11 = do do return (Atom (B False))
                                                                                                                                                 in case kl_V1543t of
                                                                                                                                                        !(kl_V1543t@(Cons (!kl_V1543th)
                                                                                                                                                                          (!kl_V1543tt))) -> pat_cond_5 kl_V1543t kl_V1543th kl_V1543tt
                                                                                                                                                        _ -> pat_cond_11
                                                                                                                                    case kl_if_4 of
                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                    pat_cond_12 = do do return (Atom (B False))
                                                                                                                 in case kl_V1543h of
                                                                                                                        kl_V1543h@(Atom (UnboundSym "compile")) -> pat_cond_3
                                                                                                                        kl_V1543h@(ApplC (PL "compile"
                                                                                                                                             _)) -> pat_cond_3
                                                                                                                        kl_V1543h@(ApplC (Func "compile"
                                                                                                                                               _)) -> pat_cond_3
                                                                                                                        _ -> pat_cond_12
                                                                                                    case kl_if_2 of
                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                        _ -> throwError "if: expected boolean"
                                                       pat_cond_13 = do do return (Atom (B False))
                                                    in case kl_V1543 of
                                                           !(kl_V1543@(Cons (!kl_V1543h)
                                                                            (!kl_V1543t))) -> pat_cond_1 kl_V1543 kl_V1543h kl_V1543t
                                                           _ -> pat_cond_13
                                       case kl_if_0 of
                                           Atom (B (True)) -> do !appl_14 <- kl_V1543 `pseq` tl kl_V1543
                                                                 !appl_15 <- appl_14 `pseq` hd appl_14
                                                                 !appl_16 <- kl_V1543 `pseq` tl kl_V1543
                                                                 !appl_17 <- appl_16 `pseq` tl appl_16
                                                                 !appl_18 <- appl_17 `pseq` hd appl_17
                                                                 let !appl_19 = Atom Nil
                                                                 !appl_20 <- appl_19 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "E")) appl_19
                                                                 !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_20
                                                                 let !appl_22 = Atom Nil
                                                                 !appl_23 <- appl_22 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "E")) appl_22
                                                                 !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.Str "parse error here: ~S~%")) appl_23
                                                                 !appl_25 <- appl_24 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "error")) appl_24
                                                                 let !appl_26 = Atom Nil
                                                                 !appl_27 <- appl_26 `pseq` klCons (Core.Types.Atom (Core.Types.Str "parse error~%")) appl_26
                                                                 !appl_28 <- appl_27 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "error")) appl_27
                                                                 let !appl_29 = Atom Nil
                                                                 !appl_30 <- appl_28 `pseq` (appl_29 `pseq` klCons appl_28 appl_29)
                                                                 !appl_31 <- appl_25 `pseq` (appl_30 `pseq` klCons appl_25 appl_30)
                                                                 !appl_32 <- appl_21 `pseq` (appl_31 `pseq` klCons appl_21 appl_31)
                                                                 !appl_33 <- appl_32 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_32
                                                                 let !appl_34 = Atom Nil
                                                                 !appl_35 <- appl_33 `pseq` (appl_34 `pseq` klCons appl_33 appl_34)
                                                                 !appl_36 <- appl_35 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "E")) appl_35
                                                                 !appl_37 <- appl_36 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_36
                                                                 let !appl_38 = Atom Nil
                                                                 !appl_39 <- appl_37 `pseq` (appl_38 `pseq` klCons appl_37 appl_38)
                                                                 !appl_40 <- appl_18 `pseq` (appl_39 `pseq` klCons appl_18 appl_39)
                                                                 !appl_41 <- appl_15 `pseq` (appl_40 `pseq` klCons appl_15 appl_40)
                                                                 appl_41 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_41
                                           Atom (B (False)) -> do do return kl_V1543
                                           _ -> throwError "if: expected boolean"

kl_shen_prolog_macro :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_prolog_macro (!kl_V1545) = do let pat_cond_0 kl_V1545 kl_V1545t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_F) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Receive) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_PrologDef) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Query) -> do return kl_Query)))
                                                                                                                                                                                                                                                                               let !appl_5 = Atom Nil
                                                                                                                                                                                                                                                                               !appl_6 <- appl_5 `pseq` klCons (ApplC (PL "shen.start-new-prolog-process" kl_shen_start_new_prolog_process)) appl_5
                                                                                                                                                                                                                                                                               let !appl_7 = Atom Nil
                                                                                                                                                                                                                                                                               !appl_8 <- appl_7 `pseq` klCons (Atom (B True)) appl_7
                                                                                                                                                                                                                                                                               !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "freeze")) appl_8
                                                                                                                                                                                                                                                                               let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                               !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                                                                                                                                                                                                                                               !appl_12 <- appl_6 `pseq` (appl_11 `pseq` klCons appl_6 appl_11)
                                                                                                                                                                                                                                                                               !appl_13 <- kl_Receive `pseq` (appl_12 `pseq` kl_append kl_Receive appl_12)
                                                                                                                                                                                                                                                                               !appl_14 <- kl_F `pseq` (appl_13 `pseq` klCons kl_F appl_13)
                                                                                                                                                                                                                                                                               appl_14 `pseq` applyWrapper appl_4 [appl_14])))
                                                                                                                                                                                                           let !appl_15 = Atom Nil
                                                                                                                                                                                                           !appl_16 <- kl_F `pseq` (appl_15 `pseq` klCons kl_F appl_15)
                                                                                                                                                                                                           !appl_17 <- appl_16 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defprolog")) appl_16
                                                                                                                                                                                                           let !appl_18 = Atom Nil
                                                                                                                                                                                                           !appl_19 <- appl_18 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "<--")) appl_18
                                                                                                                                                                                                           !appl_20 <- kl_V1545t `pseq` kl_shen_pass_literals kl_V1545t
                                                                                                                                                                                                           let !appl_21 = Atom Nil
                                                                                                                                                                                                           !appl_22 <- appl_21 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym ";")) appl_21
                                                                                                                                                                                                           !appl_23 <- appl_20 `pseq` (appl_22 `pseq` kl_append appl_20 appl_22)
                                                                                                                                                                                                           !appl_24 <- appl_19 `pseq` (appl_23 `pseq` kl_append appl_19 appl_23)
                                                                                                                                                                                                           !appl_25 <- kl_Receive `pseq` (appl_24 `pseq` kl_append kl_Receive appl_24)
                                                                                                                                                                                                           !appl_26 <- appl_17 `pseq` (appl_25 `pseq` kl_append appl_17 appl_25)
                                                                                                                                                                                                           !appl_27 <- appl_26 `pseq` kl_eval appl_26
                                                                                                                                                                                                           appl_27 `pseq` applyWrapper appl_3 [appl_27])))
                                                                                                                                         !appl_28 <- kl_V1545t `pseq` kl_shen_receive_terms kl_V1545t
                                                                                                                                         appl_28 `pseq` applyWrapper appl_2 [appl_28])))
                                                                             !appl_29 <- kl_gensym (Core.Types.Atom (Core.Types.UnboundSym "shen.f"))
                                                                             appl_29 `pseq` applyWrapper appl_1 [appl_29]
                                          pat_cond_30 = do do return kl_V1545
                                       in case kl_V1545 of
                                              !(kl_V1545@(Cons (Atom (UnboundSym "prolog?"))
                                                               (!kl_V1545t))) -> pat_cond_0 kl_V1545 kl_V1545t
                                              !(kl_V1545@(Cons (ApplC (PL "prolog?" _))
                                                               (!kl_V1545t))) -> pat_cond_0 kl_V1545 kl_V1545t
                                              !(kl_V1545@(Cons (ApplC (Func "prolog?" _))
                                                               (!kl_V1545t))) -> pat_cond_0 kl_V1545 kl_V1545t
                                              _ -> pat_cond_30

kl_shen_receive_terms :: Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_receive_terms (!kl_V1551) = do let !appl_0 = Atom Nil
                                       !kl_if_1 <- appl_0 `pseq` (kl_V1551 `pseq` eq appl_0 kl_V1551)
                                       case kl_if_1 of
                                           Atom (B (True)) -> do return (Atom Nil)
                                           Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V1551 kl_V1551h kl_V1551t = do !kl_if_4 <- let pat_cond_5 kl_V1551h kl_V1551hh kl_V1551ht = do !kl_if_6 <- let pat_cond_7 = do !kl_if_8 <- let pat_cond_9 kl_V1551ht kl_V1551hth kl_V1551htt = do let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                                                  !kl_if_11 <- appl_10 `pseq` (kl_V1551htt `pseq` eq appl_10 kl_V1551htt)
                                                                                                                                                                                                                                                                                                  case kl_if_11 of
                                                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                               pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                            in case kl_V1551ht of
                                                                                                                                                                                                                                                   !(kl_V1551ht@(Cons (!kl_V1551hth)
                                                                                                                                                                                                                                                                      (!kl_V1551htt))) -> pat_cond_9 kl_V1551ht kl_V1551hth kl_V1551htt
                                                                                                                                                                                                                                                   _ -> pat_cond_12
                                                                                                                                                                                                                               case kl_if_8 of
                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                               pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                            in case kl_V1551hh of
                                                                                                                                                                                                                   kl_V1551hh@(Atom (UnboundSym "receive")) -> pat_cond_7
                                                                                                                                                                                                                   kl_V1551hh@(ApplC (PL "receive"
                                                                                                                                                                                                                                         _)) -> pat_cond_7
                                                                                                                                                                                                                   kl_V1551hh@(ApplC (Func "receive"
                                                                                                                                                                                                                                           _)) -> pat_cond_7
                                                                                                                                                                                                                   _ -> pat_cond_13
                                                                                                                                                                                               case kl_if_6 of
                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                               pat_cond_14 = do do return (Atom (B False))
                                                                                                                                            in case kl_V1551h of
                                                                                                                                                   !(kl_V1551h@(Cons (!kl_V1551hh)
                                                                                                                                                                     (!kl_V1551ht))) -> pat_cond_5 kl_V1551h kl_V1551hh kl_V1551ht
                                                                                                                                                   _ -> pat_cond_14
                                                                                                                               case kl_if_4 of
                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                  pat_cond_15 = do do return (Atom (B False))
                                                                               in case kl_V1551 of
                                                                                      !(kl_V1551@(Cons (!kl_V1551h)
                                                                                                       (!kl_V1551t))) -> pat_cond_3 kl_V1551 kl_V1551h kl_V1551t
                                                                                      _ -> pat_cond_15
                                                                  case kl_if_2 of
                                                                      Atom (B (True)) -> do !appl_16 <- kl_V1551 `pseq` hd kl_V1551
                                                                                            !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                            !appl_18 <- appl_17 `pseq` hd appl_17
                                                                                            !appl_19 <- kl_V1551 `pseq` tl kl_V1551
                                                                                            !appl_20 <- appl_19 `pseq` kl_shen_receive_terms appl_19
                                                                                            appl_18 `pseq` (appl_20 `pseq` klCons appl_18 appl_20)
                                                                      Atom (B (False)) -> do let pat_cond_21 kl_V1551 kl_V1551h kl_V1551t = do kl_V1551t `pseq` kl_shen_receive_terms kl_V1551t
                                                                                                 pat_cond_22 = do do kl_shen_f_error (ApplC (wrapNamed "shen.receive-terms" kl_shen_receive_terms))
                                                                                              in case kl_V1551 of
                                                                                                     !(kl_V1551@(Cons (!kl_V1551h)
                                                                                                                      (!kl_V1551t))) -> pat_cond_21 kl_V1551 kl_V1551h kl_V1551t
                                                                                                     _ -> pat_cond_22
                                                                      _ -> throwError "if: expected boolean"
                                           _ -> throwError "if: expected boolean"

kl_shen_pass_literals :: Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_pass_literals (!kl_V1555) = do let !appl_0 = Atom Nil
                                       !kl_if_1 <- appl_0 `pseq` (kl_V1555 `pseq` eq appl_0 kl_V1555)
                                       case kl_if_1 of
                                           Atom (B (True)) -> do return (Atom Nil)
                                           Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V1555 kl_V1555h kl_V1555t = do !kl_if_4 <- let pat_cond_5 kl_V1555h kl_V1555hh kl_V1555ht = do !kl_if_6 <- let pat_cond_7 = do !kl_if_8 <- let pat_cond_9 kl_V1555ht kl_V1555hth kl_V1555htt = do let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                                                  !kl_if_11 <- appl_10 `pseq` (kl_V1555htt `pseq` eq appl_10 kl_V1555htt)
                                                                                                                                                                                                                                                                                                  case kl_if_11 of
                                                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                               pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                            in case kl_V1555ht of
                                                                                                                                                                                                                                                   !(kl_V1555ht@(Cons (!kl_V1555hth)
                                                                                                                                                                                                                                                                      (!kl_V1555htt))) -> pat_cond_9 kl_V1555ht kl_V1555hth kl_V1555htt
                                                                                                                                                                                                                                                   _ -> pat_cond_12
                                                                                                                                                                                                                               case kl_if_8 of
                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                               pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                            in case kl_V1555hh of
                                                                                                                                                                                                                   kl_V1555hh@(Atom (UnboundSym "receive")) -> pat_cond_7
                                                                                                                                                                                                                   kl_V1555hh@(ApplC (PL "receive"
                                                                                                                                                                                                                                         _)) -> pat_cond_7
                                                                                                                                                                                                                   kl_V1555hh@(ApplC (Func "receive"
                                                                                                                                                                                                                                           _)) -> pat_cond_7
                                                                                                                                                                                                                   _ -> pat_cond_13
                                                                                                                                                                                               case kl_if_6 of
                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                               pat_cond_14 = do do return (Atom (B False))
                                                                                                                                            in case kl_V1555h of
                                                                                                                                                   !(kl_V1555h@(Cons (!kl_V1555hh)
                                                                                                                                                                     (!kl_V1555ht))) -> pat_cond_5 kl_V1555h kl_V1555hh kl_V1555ht
                                                                                                                                                   _ -> pat_cond_14
                                                                                                                               case kl_if_4 of
                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                  pat_cond_15 = do do return (Atom (B False))
                                                                               in case kl_V1555 of
                                                                                      !(kl_V1555@(Cons (!kl_V1555h)
                                                                                                       (!kl_V1555t))) -> pat_cond_3 kl_V1555 kl_V1555h kl_V1555t
                                                                                      _ -> pat_cond_15
                                                                  case kl_if_2 of
                                                                      Atom (B (True)) -> do !appl_16 <- kl_V1555 `pseq` tl kl_V1555
                                                                                            appl_16 `pseq` kl_shen_pass_literals appl_16
                                                                      Atom (B (False)) -> do let pat_cond_17 kl_V1555 kl_V1555h kl_V1555t = do !appl_18 <- kl_V1555t `pseq` kl_shen_pass_literals kl_V1555t
                                                                                                                                               kl_V1555h `pseq` (appl_18 `pseq` klCons kl_V1555h appl_18)
                                                                                                 pat_cond_19 = do do kl_shen_f_error (ApplC (wrapNamed "shen.pass-literals" kl_shen_pass_literals))
                                                                                              in case kl_V1555 of
                                                                                                     !(kl_V1555@(Cons (!kl_V1555h)
                                                                                                                      (!kl_V1555t))) -> pat_cond_17 kl_V1555 kl_V1555h kl_V1555t
                                                                                                     _ -> pat_cond_19
                                                                      _ -> throwError "if: expected boolean"
                                           _ -> throwError "if: expected boolean"

kl_shen_defprolog_macro :: Core.Types.KLValue ->
                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_defprolog_macro (!kl_V1557) = do let pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do kl_Y `pseq` kl_shen_LBdefprologRB kl_Y)))
                                                                                                      let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do kl_V1557th `pseq` (kl_Y `pseq` kl_shen_prolog_error kl_V1557th kl_Y))))
                                                                                                      appl_1 `pseq` (kl_V1557t `pseq` (appl_2 `pseq` kl_compile appl_1 kl_V1557t appl_2))
                                             pat_cond_3 = do do return kl_V1557
                                          in case kl_V1557 of
                                                 !(kl_V1557@(Cons (Atom (UnboundSym "defprolog"))
                                                                  (!(kl_V1557t@(Cons (!kl_V1557th)
                                                                                     (!kl_V1557tt)))))) -> pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt
                                                 !(kl_V1557@(Cons (ApplC (PL "defprolog" _))
                                                                  (!(kl_V1557t@(Cons (!kl_V1557th)
                                                                                     (!kl_V1557tt)))))) -> pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt
                                                 !(kl_V1557@(Cons (ApplC (Func "defprolog" _))
                                                                  (!(kl_V1557t@(Cons (!kl_V1557th)
                                                                                     (!kl_V1557tt)))))) -> pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt
                                                 _ -> pat_cond_3

kl_shen_datatype_macro :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_datatype_macro (!kl_V1559) = do let pat_cond_0 kl_V1559 kl_V1559t kl_V1559th kl_V1559tt = do !appl_1 <- kl_V1559th `pseq` kl_shen_intern_type kl_V1559th
                                                                                                     let !appl_2 = Atom Nil
                                                                                                     !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_2
                                                                                                     !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "shen.<datatype-rules>" kl_shen_LBdatatype_rulesRB)) appl_3
                                                                                                     let !appl_5 = Atom Nil
                                                                                                     !appl_6 <- appl_4 `pseq` (appl_5 `pseq` klCons appl_4 appl_5)
                                                                                                     !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "X")) appl_6
                                                                                                     !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_7
                                                                                                     !appl_9 <- kl_V1559tt `pseq` kl_shen_rcons_form kl_V1559tt
                                                                                                     let !appl_10 = Atom Nil
                                                                                                     !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "shen.datatype-error" kl_shen_datatype_error)) appl_10
                                                                                                     !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "function" kl_function)) appl_11
                                                                                                     let !appl_13 = Atom Nil
                                                                                                     !appl_14 <- appl_12 `pseq` (appl_13 `pseq` klCons appl_12 appl_13)
                                                                                                     !appl_15 <- appl_9 `pseq` (appl_14 `pseq` klCons appl_9 appl_14)
                                                                                                     !appl_16 <- appl_8 `pseq` (appl_15 `pseq` klCons appl_8 appl_15)
                                                                                                     !appl_17 <- appl_16 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_16
                                                                                                     let !appl_18 = Atom Nil
                                                                                                     !appl_19 <- appl_17 `pseq` (appl_18 `pseq` klCons appl_17 appl_18)
                                                                                                     !appl_20 <- appl_1 `pseq` (appl_19 `pseq` klCons appl_1 appl_19)
                                                                                                     appl_20 `pseq` klCons (ApplC (wrapNamed "shen.process-datatype" kl_shen_process_datatype)) appl_20
                                            pat_cond_21 = do do return kl_V1559
                                         in case kl_V1559 of
                                                !(kl_V1559@(Cons (Atom (UnboundSym "datatype"))
                                                                 (!(kl_V1559t@(Cons (!kl_V1559th)
                                                                                    (!kl_V1559tt)))))) -> pat_cond_0 kl_V1559 kl_V1559t kl_V1559th kl_V1559tt
                                                !(kl_V1559@(Cons (ApplC (PL "datatype" _))
                                                                 (!(kl_V1559t@(Cons (!kl_V1559th)
                                                                                    (!kl_V1559tt)))))) -> pat_cond_0 kl_V1559 kl_V1559t kl_V1559th kl_V1559tt
                                                !(kl_V1559@(Cons (ApplC (Func "datatype" _))
                                                                 (!(kl_V1559t@(Cons (!kl_V1559th)
                                                                                    (!kl_V1559tt)))))) -> pat_cond_0 kl_V1559 kl_V1559t kl_V1559th kl_V1559tt
                                                _ -> pat_cond_21

kl_shen_intern_type :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_intern_type (!kl_V1561) = do !appl_0 <- kl_V1561 `pseq` str kl_V1561
                                     !appl_1 <- appl_0 `pseq` cn (Core.Types.Atom (Core.Types.Str "type#")) appl_0
                                     appl_1 `pseq` intern appl_1

kl_shen_Ats_macro :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_Ats_macro (!kl_V1563) = do let pat_cond_0 kl_V1563 kl_V1563t kl_V1563th kl_V1563tt kl_V1563tth kl_V1563ttt kl_V1563ttth kl_V1563tttt = do !appl_1 <- kl_V1563tt `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) kl_V1563tt
                                                                                                                                                  !appl_2 <- appl_1 `pseq` kl_shen_Ats_macro appl_1
                                                                                                                                                  let !appl_3 = Atom Nil
                                                                                                                                                  !appl_4 <- appl_2 `pseq` (appl_3 `pseq` klCons appl_2 appl_3)
                                                                                                                                                  !appl_5 <- kl_V1563th `pseq` (appl_4 `pseq` klCons kl_V1563th appl_4)
                                                                                                                                                  appl_5 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_5
                                       pat_cond_6 = do !kl_if_7 <- let pat_cond_8 kl_V1563 kl_V1563h kl_V1563t = do !kl_if_9 <- let pat_cond_10 = do !kl_if_11 <- let pat_cond_12 kl_V1563t kl_V1563th kl_V1563tt = do !kl_if_13 <- let pat_cond_14 kl_V1563tt kl_V1563tth kl_V1563ttt = do let !appl_15 = Atom Nil
                                                                                                                                                                                                                                                                                            !kl_if_16 <- appl_15 `pseq` (kl_V1563ttt `pseq` eq appl_15 kl_V1563ttt)
                                                                                                                                                                                                                                                                                            !kl_if_17 <- case kl_if_16 of
                                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do !kl_if_18 <- kl_V1563th `pseq` stringP kl_V1563th
                                                                                                                                                                                                                                                                                                                                   case kl_if_18 of
                                                                                                                                                                                                                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                            case kl_if_17 of
                                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                        pat_cond_19 = do do return (Atom (B False))
                                                                                                                                                                                                                                     in case kl_V1563tt of
                                                                                                                                                                                                                                            !(kl_V1563tt@(Cons (!kl_V1563tth)
                                                                                                                                                                                                                                                               (!kl_V1563ttt))) -> pat_cond_14 kl_V1563tt kl_V1563tth kl_V1563ttt
                                                                                                                                                                                                                                            _ -> pat_cond_19
                                                                                                                                                                                                                       case kl_if_13 of
                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                      pat_cond_20 = do do return (Atom (B False))
                                                                                                                                                                   in case kl_V1563t of
                                                                                                                                                                          !(kl_V1563t@(Cons (!kl_V1563th)
                                                                                                                                                                                            (!kl_V1563tt))) -> pat_cond_12 kl_V1563t kl_V1563th kl_V1563tt
                                                                                                                                                                          _ -> pat_cond_20
                                                                                                                                                     case kl_if_11 of
                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                    pat_cond_21 = do do return (Atom (B False))
                                                                                                                                 in case kl_V1563h of
                                                                                                                                        kl_V1563h@(Atom (UnboundSym "@s")) -> pat_cond_10
                                                                                                                                        kl_V1563h@(ApplC (PL "@s"
                                                                                                                                                             _)) -> pat_cond_10
                                                                                                                                        kl_V1563h@(ApplC (Func "@s"
                                                                                                                                                               _)) -> pat_cond_10
                                                                                                                                        _ -> pat_cond_21
                                                                                                                    case kl_if_9 of
                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                        _ -> throwError "if: expected boolean"
                                                                       pat_cond_22 = do do return (Atom (B False))
                                                                    in case kl_V1563 of
                                                                           !(kl_V1563@(Cons (!kl_V1563h)
                                                                                            (!kl_V1563t))) -> pat_cond_8 kl_V1563 kl_V1563h kl_V1563t
                                                                           _ -> pat_cond_22
                                                       case kl_if_7 of
                                                           Atom (B (True)) -> do let !appl_23 = ApplC (Func "lambda" (Context (\(!kl_E) -> do !appl_24 <- kl_E `pseq` kl_length kl_E
                                                                                                                                              !kl_if_25 <- appl_24 `pseq` greaterThan appl_24 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                              case kl_if_25 of
                                                                                                                                                  Atom (B (True)) -> do !appl_26 <- kl_V1563 `pseq` tl kl_V1563
                                                                                                                                                                        !appl_27 <- appl_26 `pseq` tl appl_26
                                                                                                                                                                        !appl_28 <- kl_E `pseq` (appl_27 `pseq` kl_append kl_E appl_27)
                                                                                                                                                                        !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_28
                                                                                                                                                                        appl_29 `pseq` kl_shen_Ats_macro appl_29
                                                                                                                                                  Atom (B (False)) -> do do return kl_V1563
                                                                                                                                                  _ -> throwError "if: expected boolean")))
                                                                                 !appl_30 <- kl_V1563 `pseq` tl kl_V1563
                                                                                 !appl_31 <- appl_30 `pseq` hd appl_30
                                                                                 !appl_32 <- appl_31 `pseq` kl_explode appl_31
                                                                                 appl_32 `pseq` applyWrapper appl_23 [appl_32]
                                                           Atom (B (False)) -> do do return kl_V1563
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V1563 of
                                           !(kl_V1563@(Cons (Atom (UnboundSym "@s"))
                                                            (!(kl_V1563t@(Cons (!kl_V1563th)
                                                                               (!(kl_V1563tt@(Cons (!kl_V1563tth)
                                                                                                   (!(kl_V1563ttt@(Cons (!kl_V1563ttth)
                                                                                                                        (!kl_V1563tttt)))))))))))) -> pat_cond_0 kl_V1563 kl_V1563t kl_V1563th kl_V1563tt kl_V1563tth kl_V1563ttt kl_V1563ttth kl_V1563tttt
                                           !(kl_V1563@(Cons (ApplC (PL "@s" _))
                                                            (!(kl_V1563t@(Cons (!kl_V1563th)
                                                                               (!(kl_V1563tt@(Cons (!kl_V1563tth)
                                                                                                   (!(kl_V1563ttt@(Cons (!kl_V1563ttth)
                                                                                                                        (!kl_V1563tttt)))))))))))) -> pat_cond_0 kl_V1563 kl_V1563t kl_V1563th kl_V1563tt kl_V1563tth kl_V1563ttt kl_V1563ttth kl_V1563tttt
                                           !(kl_V1563@(Cons (ApplC (Func "@s" _))
                                                            (!(kl_V1563t@(Cons (!kl_V1563th)
                                                                               (!(kl_V1563tt@(Cons (!kl_V1563tth)
                                                                                                   (!(kl_V1563ttt@(Cons (!kl_V1563ttth)
                                                                                                                        (!kl_V1563tttt)))))))))))) -> pat_cond_0 kl_V1563 kl_V1563t kl_V1563th kl_V1563tt kl_V1563tth kl_V1563ttt kl_V1563ttth kl_V1563tttt
                                           _ -> pat_cond_6

kl_shen_synonyms_macro :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_synonyms_macro (!kl_V1565) = do let pat_cond_0 kl_V1565 kl_V1565t = do !appl_1 <- kl_V1565t `pseq` kl_shen_curry_synonyms kl_V1565t
                                                                               !appl_2 <- appl_1 `pseq` kl_shen_rcons_form appl_1
                                                                               let !appl_3 = Atom Nil
                                                                               !appl_4 <- appl_2 `pseq` (appl_3 `pseq` klCons appl_2 appl_3)
                                                                               appl_4 `pseq` klCons (ApplC (wrapNamed "shen.synonyms-help" kl_shen_synonyms_help)) appl_4
                                            pat_cond_5 = do do return kl_V1565
                                         in case kl_V1565 of
                                                !(kl_V1565@(Cons (Atom (UnboundSym "synonyms"))
                                                                 (!kl_V1565t))) -> pat_cond_0 kl_V1565 kl_V1565t
                                                !(kl_V1565@(Cons (ApplC (PL "synonyms" _))
                                                                 (!kl_V1565t))) -> pat_cond_0 kl_V1565 kl_V1565t
                                                !(kl_V1565@(Cons (ApplC (Func "synonyms" _))
                                                                 (!kl_V1565t))) -> pat_cond_0 kl_V1565 kl_V1565t
                                                _ -> pat_cond_5

kl_shen_curry_synonyms :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_curry_synonyms (!kl_V1567) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_curry_type kl_X)))
                                        appl_0 `pseq` (kl_V1567 `pseq` kl_map appl_0 kl_V1567)

kl_shen_nl_macro :: Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_nl_macro (!kl_V1569) = do !kl_if_0 <- let pat_cond_1 kl_V1569 kl_V1569h kl_V1569t = do !kl_if_2 <- let pat_cond_3 = do let !appl_4 = Atom Nil
                                                                                                                               !kl_if_5 <- appl_4 `pseq` (kl_V1569t `pseq` eq appl_4 kl_V1569t)
                                                                                                                               case kl_if_5 of
                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                               pat_cond_6 = do do return (Atom (B False))
                                                                                                            in case kl_V1569h of
                                                                                                                   kl_V1569h@(Atom (UnboundSym "nl")) -> pat_cond_3
                                                                                                                   kl_V1569h@(ApplC (PL "nl"
                                                                                                                                        _)) -> pat_cond_3
                                                                                                                   kl_V1569h@(ApplC (Func "nl"
                                                                                                                                          _)) -> pat_cond_3
                                                                                                                   _ -> pat_cond_6
                                                                                               case kl_if_2 of
                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                   _ -> throwError "if: expected boolean"
                                                  pat_cond_7 = do do return (Atom (B False))
                                               in case kl_V1569 of
                                                      !(kl_V1569@(Cons (!kl_V1569h)
                                                                       (!kl_V1569t))) -> pat_cond_1 kl_V1569 kl_V1569h kl_V1569t
                                                      _ -> pat_cond_7
                                  case kl_if_0 of
                                      Atom (B (True)) -> do let !appl_8 = Atom Nil
                                                            !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_8
                                                            appl_9 `pseq` klCons (ApplC (wrapNamed "nl" kl_nl)) appl_9
                                      Atom (B (False)) -> do do return kl_V1569
                                      _ -> throwError "if: expected boolean"

kl_shen_assoc_macro :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_assoc_macro (!kl_V1571) = do !kl_if_0 <- let pat_cond_1 kl_V1571 kl_V1571h kl_V1571t = do !kl_if_2 <- let pat_cond_3 kl_V1571t kl_V1571th kl_V1571tt = do !kl_if_4 <- let pat_cond_5 kl_V1571tt kl_V1571tth kl_V1571ttt = do !kl_if_6 <- let pat_cond_7 kl_V1571ttt kl_V1571ttth kl_V1571tttt = do let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                                                           !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_8
                                                                                                                                                                                                                                                                                                           !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_9
                                                                                                                                                                                                                                                                                                           !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_10
                                                                                                                                                                                                                                                                                                           !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "or")) appl_11
                                                                                                                                                                                                                                                                                                           !appl_13 <- appl_12 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "and")) appl_12
                                                                                                                                                                                                                                                                                                           !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_13
                                                                                                                                                                                                                                                                                                           !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_14
                                                                                                                                                                                                                                                                                                           !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_15
                                                                                                                                                                                                                                                                                                           !kl_if_17 <- kl_V1571h `pseq` (appl_16 `pseq` kl_elementP kl_V1571h appl_16)
                                                                                                                                                                                                                                                                                                           case kl_if_17 of
                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                     pat_cond_18 = do do return (Atom (B False))
                                                                                                                                                                                                                                                  in case kl_V1571ttt of
                                                                                                                                                                                                                                                         !(kl_V1571ttt@(Cons (!kl_V1571ttth)
                                                                                                                                                                                                                                                                             (!kl_V1571tttt))) -> pat_cond_7 kl_V1571ttt kl_V1571ttth kl_V1571tttt
                                                                                                                                                                                                                                                         _ -> pat_cond_18
                                                                                                                                                                                                                                     case kl_if_6 of
                                                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                                                  pat_cond_19 = do do return (Atom (B False))
                                                                                                                                                                               in case kl_V1571tt of
                                                                                                                                                                                      !(kl_V1571tt@(Cons (!kl_V1571tth)
                                                                                                                                                                                                         (!kl_V1571ttt))) -> pat_cond_5 kl_V1571tt kl_V1571tth kl_V1571ttt
                                                                                                                                                                                      _ -> pat_cond_19
                                                                                                                                                                  case kl_if_4 of
                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                  pat_cond_20 = do do return (Atom (B False))
                                                                                                               in case kl_V1571t of
                                                                                                                      !(kl_V1571t@(Cons (!kl_V1571th)
                                                                                                                                        (!kl_V1571tt))) -> pat_cond_3 kl_V1571t kl_V1571th kl_V1571tt
                                                                                                                      _ -> pat_cond_20
                                                                                                  case kl_if_2 of
                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                      _ -> throwError "if: expected boolean"
                                                     pat_cond_21 = do do return (Atom (B False))
                                                  in case kl_V1571 of
                                                         !(kl_V1571@(Cons (!kl_V1571h)
                                                                          (!kl_V1571t))) -> pat_cond_1 kl_V1571 kl_V1571h kl_V1571t
                                                         _ -> pat_cond_21
                                     case kl_if_0 of
                                         Atom (B (True)) -> do !appl_22 <- kl_V1571 `pseq` hd kl_V1571
                                                               !appl_23 <- kl_V1571 `pseq` tl kl_V1571
                                                               !appl_24 <- appl_23 `pseq` hd appl_23
                                                               !appl_25 <- kl_V1571 `pseq` hd kl_V1571
                                                               !appl_26 <- kl_V1571 `pseq` tl kl_V1571
                                                               !appl_27 <- appl_26 `pseq` tl appl_26
                                                               !appl_28 <- appl_25 `pseq` (appl_27 `pseq` klCons appl_25 appl_27)
                                                               !appl_29 <- appl_28 `pseq` kl_shen_assoc_macro appl_28
                                                               let !appl_30 = Atom Nil
                                                               !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                                                               !appl_32 <- appl_24 `pseq` (appl_31 `pseq` klCons appl_24 appl_31)
                                                               appl_22 `pseq` (appl_32 `pseq` klCons appl_22 appl_32)
                                         Atom (B (False)) -> do do return kl_V1571
                                         _ -> throwError "if: expected boolean"

kl_shen_let_macro :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_let_macro (!kl_V1573) = do let pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt kl_V1573tttth kl_V1573ttttt = do !appl_1 <- kl_V1573ttt `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) kl_V1573ttt
                                                                                                                                                                              !appl_2 <- appl_1 `pseq` kl_shen_let_macro appl_1
                                                                                                                                                                              let !appl_3 = Atom Nil
                                                                                                                                                                              !appl_4 <- appl_2 `pseq` (appl_3 `pseq` klCons appl_2 appl_3)
                                                                                                                                                                              !appl_5 <- kl_V1573tth `pseq` (appl_4 `pseq` klCons kl_V1573tth appl_4)
                                                                                                                                                                              !appl_6 <- kl_V1573th `pseq` (appl_5 `pseq` klCons kl_V1573th appl_5)
                                                                                                                                                                              appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_6
                                       pat_cond_7 = do do return kl_V1573
                                    in case kl_V1573 of
                                           !(kl_V1573@(Cons (Atom (UnboundSym "let"))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (!(kl_V1573ttt@(Cons (!kl_V1573ttth)
                                                                                                                        (!(kl_V1573tttt@(Cons (!kl_V1573tttth)
                                                                                                                                              (!kl_V1573ttttt))))))))))))))) -> pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt kl_V1573tttth kl_V1573ttttt
                                           !(kl_V1573@(Cons (ApplC (PL "let" _))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (!(kl_V1573ttt@(Cons (!kl_V1573ttth)
                                                                                                                        (!(kl_V1573tttt@(Cons (!kl_V1573tttth)
                                                                                                                                              (!kl_V1573ttttt))))))))))))))) -> pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt kl_V1573tttth kl_V1573ttttt
                                           !(kl_V1573@(Cons (ApplC (Func "let" _))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (!(kl_V1573ttt@(Cons (!kl_V1573ttth)
                                                                                                                        (!(kl_V1573tttt@(Cons (!kl_V1573tttth)
                                                                                                                                              (!kl_V1573ttttt))))))))))))))) -> pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt kl_V1573tttth kl_V1573ttttt
                                           _ -> pat_cond_7

kl_shen_abs_macro :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_abs_macro (!kl_V1575) = do let pat_cond_0 kl_V1575 kl_V1575t kl_V1575th kl_V1575tt kl_V1575tth kl_V1575ttt kl_V1575ttth kl_V1575tttt = do !appl_1 <- kl_V1575tt `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "/.")) kl_V1575tt
                                                                                                                                                  !appl_2 <- appl_1 `pseq` kl_shen_abs_macro appl_1
                                                                                                                                                  let !appl_3 = Atom Nil
                                                                                                                                                  !appl_4 <- appl_2 `pseq` (appl_3 `pseq` klCons appl_2 appl_3)
                                                                                                                                                  !appl_5 <- kl_V1575th `pseq` (appl_4 `pseq` klCons kl_V1575th appl_4)
                                                                                                                                                  appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_5
                                       pat_cond_6 = do !kl_if_7 <- let pat_cond_8 kl_V1575 kl_V1575h kl_V1575t = do !kl_if_9 <- let pat_cond_10 = do !kl_if_11 <- let pat_cond_12 kl_V1575t kl_V1575th kl_V1575tt = do !kl_if_13 <- let pat_cond_14 kl_V1575tt kl_V1575tth kl_V1575ttt = do let !appl_15 = Atom Nil
                                                                                                                                                                                                                                                                                            !kl_if_16 <- appl_15 `pseq` (kl_V1575ttt `pseq` eq appl_15 kl_V1575ttt)
                                                                                                                                                                                                                                                                                            case kl_if_16 of
                                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                        pat_cond_17 = do do return (Atom (B False))
                                                                                                                                                                                                                                     in case kl_V1575tt of
                                                                                                                                                                                                                                            !(kl_V1575tt@(Cons (!kl_V1575tth)
                                                                                                                                                                                                                                                               (!kl_V1575ttt))) -> pat_cond_14 kl_V1575tt kl_V1575tth kl_V1575ttt
                                                                                                                                                                                                                                            _ -> pat_cond_17
                                                                                                                                                                                                                       case kl_if_13 of
                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                      pat_cond_18 = do do return (Atom (B False))
                                                                                                                                                                   in case kl_V1575t of
                                                                                                                                                                          !(kl_V1575t@(Cons (!kl_V1575th)
                                                                                                                                                                                            (!kl_V1575tt))) -> pat_cond_12 kl_V1575t kl_V1575th kl_V1575tt
                                                                                                                                                                          _ -> pat_cond_18
                                                                                                                                                     case kl_if_11 of
                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                    pat_cond_19 = do do return (Atom (B False))
                                                                                                                                 in case kl_V1575h of
                                                                                                                                        kl_V1575h@(Atom (UnboundSym "/.")) -> pat_cond_10
                                                                                                                                        kl_V1575h@(ApplC (PL "/."
                                                                                                                                                             _)) -> pat_cond_10
                                                                                                                                        kl_V1575h@(ApplC (Func "/."
                                                                                                                                                               _)) -> pat_cond_10
                                                                                                                                        _ -> pat_cond_19
                                                                                                                    case kl_if_9 of
                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                        _ -> throwError "if: expected boolean"
                                                                       pat_cond_20 = do do return (Atom (B False))
                                                                    in case kl_V1575 of
                                                                           !(kl_V1575@(Cons (!kl_V1575h)
                                                                                            (!kl_V1575t))) -> pat_cond_8 kl_V1575 kl_V1575h kl_V1575t
                                                                           _ -> pat_cond_20
                                                       case kl_if_7 of
                                                           Atom (B (True)) -> do !appl_21 <- kl_V1575 `pseq` tl kl_V1575
                                                                                 appl_21 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "lambda")) appl_21
                                                           Atom (B (False)) -> do do return kl_V1575
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V1575 of
                                           !(kl_V1575@(Cons (Atom (UnboundSym "/."))
                                                            (!(kl_V1575t@(Cons (!kl_V1575th)
                                                                               (!(kl_V1575tt@(Cons (!kl_V1575tth)
                                                                                                   (!(kl_V1575ttt@(Cons (!kl_V1575ttth)
                                                                                                                        (!kl_V1575tttt)))))))))))) -> pat_cond_0 kl_V1575 kl_V1575t kl_V1575th kl_V1575tt kl_V1575tth kl_V1575ttt kl_V1575ttth kl_V1575tttt
                                           !(kl_V1575@(Cons (ApplC (PL "/." _))
                                                            (!(kl_V1575t@(Cons (!kl_V1575th)
                                                                               (!(kl_V1575tt@(Cons (!kl_V1575tth)
                                                                                                   (!(kl_V1575ttt@(Cons (!kl_V1575ttth)
                                                                                                                        (!kl_V1575tttt)))))))))))) -> pat_cond_0 kl_V1575 kl_V1575t kl_V1575th kl_V1575tt kl_V1575tth kl_V1575ttt kl_V1575ttth kl_V1575tttt
                                           !(kl_V1575@(Cons (ApplC (Func "/." _))
                                                            (!(kl_V1575t@(Cons (!kl_V1575th)
                                                                               (!(kl_V1575tt@(Cons (!kl_V1575tth)
                                                                                                   (!(kl_V1575ttt@(Cons (!kl_V1575ttth)
                                                                                                                        (!kl_V1575tttt)))))))))))) -> pat_cond_0 kl_V1575 kl_V1575t kl_V1575th kl_V1575tt kl_V1575tth kl_V1575ttt kl_V1575ttth kl_V1575tttt
                                           _ -> pat_cond_6

kl_shen_cases_macro :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_cases_macro (!kl_V1579) = do let pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt = do return kl_V1579tth
                                         pat_cond_1 = do !kl_if_2 <- let pat_cond_3 kl_V1579 kl_V1579h kl_V1579t = do !kl_if_4 <- let pat_cond_5 = do !kl_if_6 <- let pat_cond_7 kl_V1579t kl_V1579th kl_V1579tt = do !kl_if_8 <- let pat_cond_9 kl_V1579tt kl_V1579tth kl_V1579ttt = do let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                                         !kl_if_11 <- appl_10 `pseq` (kl_V1579ttt `pseq` eq appl_10 kl_V1579ttt)
                                                                                                                                                                                                                                                                                         case kl_if_11 of
                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                      pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                   in case kl_V1579tt of
                                                                                                                                                                                                                                          !(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                                                                                                                                                                             (!kl_V1579ttt))) -> pat_cond_9 kl_V1579tt kl_V1579tth kl_V1579ttt
                                                                                                                                                                                                                                          _ -> pat_cond_12
                                                                                                                                                                                                                      case kl_if_8 of
                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                      pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                   in case kl_V1579t of
                                                                                                                                                                          !(kl_V1579t@(Cons (!kl_V1579th)
                                                                                                                                                                                            (!kl_V1579tt))) -> pat_cond_7 kl_V1579t kl_V1579th kl_V1579tt
                                                                                                                                                                          _ -> pat_cond_13
                                                                                                                                                      case kl_if_6 of
                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                      pat_cond_14 = do do return (Atom (B False))
                                                                                                                                   in case kl_V1579h of
                                                                                                                                          kl_V1579h@(Atom (UnboundSym "cases")) -> pat_cond_5
                                                                                                                                          kl_V1579h@(ApplC (PL "cases"
                                                                                                                                                               _)) -> pat_cond_5
                                                                                                                                          kl_V1579h@(ApplC (Func "cases"
                                                                                                                                                                 _)) -> pat_cond_5
                                                                                                                                          _ -> pat_cond_14
                                                                                                                      case kl_if_4 of
                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                          _ -> throwError "if: expected boolean"
                                                                         pat_cond_15 = do do return (Atom (B False))
                                                                      in case kl_V1579 of
                                                                             !(kl_V1579@(Cons (!kl_V1579h)
                                                                                              (!kl_V1579t))) -> pat_cond_3 kl_V1579 kl_V1579h kl_V1579t
                                                                             _ -> pat_cond_15
                                                         case kl_if_2 of
                                                             Atom (B (True)) -> do !appl_16 <- kl_V1579 `pseq` tl kl_V1579
                                                                                   !appl_17 <- appl_16 `pseq` hd appl_16
                                                                                   !appl_18 <- kl_V1579 `pseq` tl kl_V1579
                                                                                   !appl_19 <- appl_18 `pseq` tl appl_18
                                                                                   !appl_20 <- appl_19 `pseq` hd appl_19
                                                                                   let !appl_21 = Atom Nil
                                                                                   !appl_22 <- appl_21 `pseq` klCons (Core.Types.Atom (Core.Types.Str "error: cases exhausted")) appl_21
                                                                                   !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_22
                                                                                   let !appl_24 = Atom Nil
                                                                                   !appl_25 <- appl_23 `pseq` (appl_24 `pseq` klCons appl_23 appl_24)
                                                                                   !appl_26 <- appl_20 `pseq` (appl_25 `pseq` klCons appl_20 appl_25)
                                                                                   !appl_27 <- appl_17 `pseq` (appl_26 `pseq` klCons appl_17 appl_26)
                                                                                   appl_27 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_27
                                                             Atom (B (False)) -> do let pat_cond_28 kl_V1579 kl_V1579t kl_V1579th kl_V1579tt kl_V1579tth kl_V1579ttt = do !appl_29 <- kl_V1579ttt `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "cases")) kl_V1579ttt
                                                                                                                                                                          !appl_30 <- appl_29 `pseq` kl_shen_cases_macro appl_29
                                                                                                                                                                          let !appl_31 = Atom Nil
                                                                                                                                                                          !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                                                                                                                          !appl_33 <- kl_V1579tth `pseq` (appl_32 `pseq` klCons kl_V1579tth appl_32)
                                                                                                                                                                          !appl_34 <- kl_V1579th `pseq` (appl_33 `pseq` klCons kl_V1579th appl_33)
                                                                                                                                                                          appl_34 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "if")) appl_34
                                                                                        pat_cond_35 = do !kl_if_36 <- let pat_cond_37 kl_V1579 kl_V1579h kl_V1579t = do !kl_if_38 <- let pat_cond_39 = do !kl_if_40 <- let pat_cond_41 kl_V1579t kl_V1579th kl_V1579tt = do let !appl_42 = Atom Nil
                                                                                                                                                                                                                                                                            !kl_if_43 <- appl_42 `pseq` (kl_V1579tt `pseq` eq appl_42 kl_V1579tt)
                                                                                                                                                                                                                                                                            case kl_if_43 of
                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                           pat_cond_44 = do do return (Atom (B False))
                                                                                                                                                                                                                        in case kl_V1579t of
                                                                                                                                                                                                                               !(kl_V1579t@(Cons (!kl_V1579th)
                                                                                                                                                                                                                                                 (!kl_V1579tt))) -> pat_cond_41 kl_V1579t kl_V1579th kl_V1579tt
                                                                                                                                                                                                                               _ -> pat_cond_44
                                                                                                                                                                                                          case kl_if_40 of
                                                                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                                                                         pat_cond_45 = do do return (Atom (B False))
                                                                                                                                                                                      in case kl_V1579h of
                                                                                                                                                                                             kl_V1579h@(Atom (UnboundSym "cases")) -> pat_cond_39
                                                                                                                                                                                             kl_V1579h@(ApplC (PL "cases"
                                                                                                                                                                                                                  _)) -> pat_cond_39
                                                                                                                                                                                             kl_V1579h@(ApplC (Func "cases"
                                                                                                                                                                                                                    _)) -> pat_cond_39
                                                                                                                                                                                             _ -> pat_cond_45
                                                                                                                                                                        case kl_if_38 of
                                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                          pat_cond_46 = do do return (Atom (B False))
                                                                                                                       in case kl_V1579 of
                                                                                                                              !(kl_V1579@(Cons (!kl_V1579h)
                                                                                                                                               (!kl_V1579t))) -> pat_cond_37 kl_V1579 kl_V1579h kl_V1579t
                                                                                                                              _ -> pat_cond_46
                                                                                                         case kl_if_36 of
                                                                                                             Atom (B (True)) -> do simpleError (Core.Types.Atom (Core.Types.Str "error: odd number of case elements\n"))
                                                                                                             Atom (B (False)) -> do do return kl_V1579
                                                                                                             _ -> throwError "if: expected boolean"
                                                                                     in case kl_V1579 of
                                                                                            !(kl_V1579@(Cons (Atom (UnboundSym "cases"))
                                                                                                             (!(kl_V1579t@(Cons (!kl_V1579th)
                                                                                                                                (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                                                                    (!kl_V1579ttt))))))))) -> pat_cond_28 kl_V1579 kl_V1579t kl_V1579th kl_V1579tt kl_V1579tth kl_V1579ttt
                                                                                            !(kl_V1579@(Cons (ApplC (PL "cases"
                                                                                                                        _))
                                                                                                             (!(kl_V1579t@(Cons (!kl_V1579th)
                                                                                                                                (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                                                                    (!kl_V1579ttt))))))))) -> pat_cond_28 kl_V1579 kl_V1579t kl_V1579th kl_V1579tt kl_V1579tth kl_V1579ttt
                                                                                            !(kl_V1579@(Cons (ApplC (Func "cases"
                                                                                                                          _))
                                                                                                             (!(kl_V1579t@(Cons (!kl_V1579th)
                                                                                                                                (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                                                                    (!kl_V1579ttt))))))))) -> pat_cond_28 kl_V1579 kl_V1579t kl_V1579th kl_V1579tt kl_V1579tth kl_V1579ttt
                                                                                            _ -> pat_cond_35
                                                             _ -> throwError "if: expected boolean"
                                      in case kl_V1579 of
                                             !(kl_V1579@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1579t@(Cons (Atom (UnboundSym "true"))
                                                                                 (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                     (!kl_V1579ttt))))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt
                                             !(kl_V1579@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1579t@(Cons (Atom (B (True)))
                                                                                 (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                     (!kl_V1579ttt))))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt
                                             !(kl_V1579@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1579t@(Cons (Atom (UnboundSym "true"))
                                                                                 (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                     (!kl_V1579ttt))))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt
                                             !(kl_V1579@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1579t@(Cons (Atom (B (True)))
                                                                                 (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                     (!kl_V1579ttt))))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt
                                             !(kl_V1579@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1579t@(Cons (Atom (UnboundSym "true"))
                                                                                 (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                     (!kl_V1579ttt))))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt
                                             !(kl_V1579@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1579t@(Cons (Atom (B (True)))
                                                                                 (!(kl_V1579tt@(Cons (!kl_V1579tth)
                                                                                                     (!kl_V1579ttt))))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579tt kl_V1579tth kl_V1579ttt
                                             _ -> pat_cond_1

kl_shen_timer_macro :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_timer_macro (!kl_V1581) = do !kl_if_0 <- let pat_cond_1 kl_V1581 kl_V1581h kl_V1581t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V1581t kl_V1581th kl_V1581tt = do let !appl_6 = Atom Nil
                                                                                                                                                                                                  !kl_if_7 <- appl_6 `pseq` (kl_V1581tt `pseq` eq appl_6 kl_V1581tt)
                                                                                                                                                                                                  case kl_if_7 of
                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                  pat_cond_8 = do do return (Atom (B False))
                                                                                                                                               in case kl_V1581t of
                                                                                                                                                      !(kl_V1581t@(Cons (!kl_V1581th)
                                                                                                                                                                        (!kl_V1581tt))) -> pat_cond_5 kl_V1581t kl_V1581th kl_V1581tt
                                                                                                                                                      _ -> pat_cond_8
                                                                                                                                  case kl_if_4 of
                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                  pat_cond_9 = do do return (Atom (B False))
                                                                                                               in case kl_V1581h of
                                                                                                                      kl_V1581h@(Atom (UnboundSym "time")) -> pat_cond_3
                                                                                                                      kl_V1581h@(ApplC (PL "time"
                                                                                                                                           _)) -> pat_cond_3
                                                                                                                      kl_V1581h@(ApplC (Func "time"
                                                                                                                                             _)) -> pat_cond_3
                                                                                                                      _ -> pat_cond_9
                                                                                                  case kl_if_2 of
                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                      _ -> throwError "if: expected boolean"
                                                     pat_cond_10 = do do return (Atom (B False))
                                                  in case kl_V1581 of
                                                         !(kl_V1581@(Cons (!kl_V1581h)
                                                                          (!kl_V1581t))) -> pat_cond_1 kl_V1581 kl_V1581h kl_V1581t
                                                         _ -> pat_cond_10
                                     case kl_if_0 of
                                         Atom (B (True)) -> do let !appl_11 = Atom Nil
                                                               !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "run")) appl_11
                                                               !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_12
                                                               !appl_14 <- kl_V1581 `pseq` tl kl_V1581
                                                               !appl_15 <- appl_14 `pseq` hd appl_14
                                                               let !appl_16 = Atom Nil
                                                               !appl_17 <- appl_16 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "run")) appl_16
                                                               !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_17
                                                               let !appl_19 = Atom Nil
                                                               !appl_20 <- appl_19 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Start")) appl_19
                                                               !appl_21 <- appl_20 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Finish")) appl_20
                                                               !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_21
                                                               let !appl_23 = Atom Nil
                                                               !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Time")) appl_23
                                                               !appl_25 <- appl_24 `pseq` klCons (ApplC (wrapNamed "str" str)) appl_24
                                                               let !appl_26 = Atom Nil
                                                               !appl_27 <- appl_26 `pseq` klCons (Core.Types.Atom (Core.Types.Str " secs\n")) appl_26
                                                               !appl_28 <- appl_25 `pseq` (appl_27 `pseq` klCons appl_25 appl_27)
                                                               !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_28
                                                               let !appl_30 = Atom Nil
                                                               !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                                                               !appl_32 <- appl_31 `pseq` klCons (Core.Types.Atom (Core.Types.Str "\nrun time: ")) appl_31
                                                               !appl_33 <- appl_32 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_32
                                                               let !appl_34 = Atom Nil
                                                               !appl_35 <- appl_34 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_34
                                                               let !appl_36 = Atom Nil
                                                               !appl_37 <- appl_35 `pseq` (appl_36 `pseq` klCons appl_35 appl_36)
                                                               !appl_38 <- appl_33 `pseq` (appl_37 `pseq` klCons appl_33 appl_37)
                                                               !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_38
                                                               let !appl_40 = Atom Nil
                                                               !appl_41 <- appl_40 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_40
                                                               !appl_42 <- appl_39 `pseq` (appl_41 `pseq` klCons appl_39 appl_41)
                                                               !appl_43 <- appl_42 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Message")) appl_42
                                                               !appl_44 <- appl_22 `pseq` (appl_43 `pseq` klCons appl_22 appl_43)
                                                               !appl_45 <- appl_44 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Time")) appl_44
                                                               !appl_46 <- appl_18 `pseq` (appl_45 `pseq` klCons appl_18 appl_45)
                                                               !appl_47 <- appl_46 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Finish")) appl_46
                                                               !appl_48 <- appl_15 `pseq` (appl_47 `pseq` klCons appl_15 appl_47)
                                                               !appl_49 <- appl_48 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_48
                                                               !appl_50 <- appl_13 `pseq` (appl_49 `pseq` klCons appl_13 appl_49)
                                                               !appl_51 <- appl_50 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Start")) appl_50
                                                               !appl_52 <- appl_51 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_51
                                                               appl_52 `pseq` kl_shen_let_macro appl_52
                                         Atom (B (False)) -> do do return kl_V1581
                                         _ -> throwError "if: expected boolean"

kl_shen_tuple_up :: Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_tuple_up (!kl_V1583) = do let pat_cond_0 kl_V1583 kl_V1583h kl_V1583t = do !appl_1 <- kl_V1583t `pseq` kl_shen_tuple_up kl_V1583t
                                                                                   let !appl_2 = Atom Nil
                                                                                   !appl_3 <- appl_1 `pseq` (appl_2 `pseq` klCons appl_1 appl_2)
                                                                                   !appl_4 <- kl_V1583h `pseq` (appl_3 `pseq` klCons kl_V1583h appl_3)
                                                                                   appl_4 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_4
                                      pat_cond_5 = do do return kl_V1583
                                   in case kl_V1583 of
                                          !(kl_V1583@(Cons (!kl_V1583h)
                                                           (!kl_V1583t))) -> pat_cond_0 kl_V1583 kl_V1583h kl_V1583t
                                          _ -> pat_cond_5

kl_shen_putDivget_macro :: Core.Types.KLValue ->
                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_putDivget_macro (!kl_V1585) = do !kl_if_0 <- let pat_cond_1 kl_V1585 kl_V1585h kl_V1585t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V1585t kl_V1585th kl_V1585tt = do !kl_if_6 <- let pat_cond_7 kl_V1585tt kl_V1585tth kl_V1585ttt = do !kl_if_8 <- let pat_cond_9 kl_V1585ttt kl_V1585ttth kl_V1585tttt = do let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                                                                                               !kl_if_11 <- appl_10 `pseq` (kl_V1585tttt `pseq` eq appl_10 kl_V1585tttt)
                                                                                                                                                                                                                                                                                                                                               case kl_if_11 of
                                                                                                                                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                         pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                      in case kl_V1585ttt of
                                                                                                                                                                                                                                                                                             !(kl_V1585ttt@(Cons (!kl_V1585ttth)
                                                                                                                                                                                                                                                                                                                 (!kl_V1585tttt))) -> pat_cond_9 kl_V1585ttt kl_V1585ttth kl_V1585tttt
                                                                                                                                                                                                                                                                                             _ -> pat_cond_12
                                                                                                                                                                                                                                                                         case kl_if_8 of
                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                      pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                                   in case kl_V1585tt of
                                                                                                                                                                                                                          !(kl_V1585tt@(Cons (!kl_V1585tth)
                                                                                                                                                                                                                                             (!kl_V1585ttt))) -> pat_cond_7 kl_V1585tt kl_V1585tth kl_V1585ttt
                                                                                                                                                                                                                          _ -> pat_cond_13
                                                                                                                                                                                                      case kl_if_6 of
                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                      pat_cond_14 = do do return (Atom (B False))
                                                                                                                                                   in case kl_V1585t of
                                                                                                                                                          !(kl_V1585t@(Cons (!kl_V1585th)
                                                                                                                                                                            (!kl_V1585tt))) -> pat_cond_5 kl_V1585t kl_V1585th kl_V1585tt
                                                                                                                                                          _ -> pat_cond_14
                                                                                                                                      case kl_if_4 of
                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                      pat_cond_15 = do do return (Atom (B False))
                                                                                                                   in case kl_V1585h of
                                                                                                                          kl_V1585h@(Atom (UnboundSym "put")) -> pat_cond_3
                                                                                                                          kl_V1585h@(ApplC (PL "put"
                                                                                                                                               _)) -> pat_cond_3
                                                                                                                          kl_V1585h@(ApplC (Func "put"
                                                                                                                                                 _)) -> pat_cond_3
                                                                                                                          _ -> pat_cond_15
                                                                                                      case kl_if_2 of
                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                          _ -> throwError "if: expected boolean"
                                                         pat_cond_16 = do do return (Atom (B False))
                                                      in case kl_V1585 of
                                                             !(kl_V1585@(Cons (!kl_V1585h)
                                                                              (!kl_V1585t))) -> pat_cond_1 kl_V1585 kl_V1585h kl_V1585t
                                                             _ -> pat_cond_16
                                         case kl_if_0 of
                                             Atom (B (True)) -> do !appl_17 <- kl_V1585 `pseq` tl kl_V1585
                                                                   !appl_18 <- appl_17 `pseq` hd appl_17
                                                                   !appl_19 <- kl_V1585 `pseq` tl kl_V1585
                                                                   !appl_20 <- appl_19 `pseq` tl appl_19
                                                                   !appl_21 <- appl_20 `pseq` hd appl_20
                                                                   !appl_22 <- kl_V1585 `pseq` tl kl_V1585
                                                                   !appl_23 <- appl_22 `pseq` tl appl_22
                                                                   !appl_24 <- appl_23 `pseq` tl appl_23
                                                                   !appl_25 <- appl_24 `pseq` hd appl_24
                                                                   let !appl_26 = Atom Nil
                                                                   !appl_27 <- appl_26 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*")) appl_26
                                                                   !appl_28 <- appl_27 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_27
                                                                   let !appl_29 = Atom Nil
                                                                   !appl_30 <- appl_28 `pseq` (appl_29 `pseq` klCons appl_28 appl_29)
                                                                   !appl_31 <- appl_25 `pseq` (appl_30 `pseq` klCons appl_25 appl_30)
                                                                   !appl_32 <- appl_21 `pseq` (appl_31 `pseq` klCons appl_21 appl_31)
                                                                   !appl_33 <- appl_18 `pseq` (appl_32 `pseq` klCons appl_18 appl_32)
                                                                   appl_33 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_33
                                             Atom (B (False)) -> do !kl_if_34 <- let pat_cond_35 kl_V1585 kl_V1585h kl_V1585t = do !kl_if_36 <- let pat_cond_37 = do !kl_if_38 <- let pat_cond_39 kl_V1585t kl_V1585th kl_V1585tt = do !kl_if_40 <- let pat_cond_41 kl_V1585tt kl_V1585tth kl_V1585ttt = do let !appl_42 = Atom Nil
                                                                                                                                                                                                                                                                                                            !kl_if_43 <- appl_42 `pseq` (kl_V1585ttt `pseq` eq appl_42 kl_V1585ttt)
                                                                                                                                                                                                                                                                                                            case kl_if_43 of
                                                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                        pat_cond_44 = do do return (Atom (B False))
                                                                                                                                                                                                                                                     in case kl_V1585tt of
                                                                                                                                                                                                                                                            !(kl_V1585tt@(Cons (!kl_V1585tth)
                                                                                                                                                                                                                                                                               (!kl_V1585ttt))) -> pat_cond_41 kl_V1585tt kl_V1585tth kl_V1585ttt
                                                                                                                                                                                                                                                            _ -> pat_cond_44
                                                                                                                                                                                                                                       case kl_if_40 of
                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                      pat_cond_45 = do do return (Atom (B False))
                                                                                                                                                                                   in case kl_V1585t of
                                                                                                                                                                                          !(kl_V1585t@(Cons (!kl_V1585th)
                                                                                                                                                                                                            (!kl_V1585tt))) -> pat_cond_39 kl_V1585t kl_V1585th kl_V1585tt
                                                                                                                                                                                          _ -> pat_cond_45
                                                                                                                                                                     case kl_if_38 of
                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                    pat_cond_46 = do do return (Atom (B False))
                                                                                                                                                 in case kl_V1585h of
                                                                                                                                                        kl_V1585h@(Atom (UnboundSym "get")) -> pat_cond_37
                                                                                                                                                        kl_V1585h@(ApplC (PL "get"
                                                                                                                                                                             _)) -> pat_cond_37
                                                                                                                                                        kl_V1585h@(ApplC (Func "get"
                                                                                                                                                                               _)) -> pat_cond_37
                                                                                                                                                        _ -> pat_cond_46
                                                                                                                                   case kl_if_36 of
                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                     pat_cond_47 = do do return (Atom (B False))
                                                                                  in case kl_V1585 of
                                                                                         !(kl_V1585@(Cons (!kl_V1585h)
                                                                                                          (!kl_V1585t))) -> pat_cond_35 kl_V1585 kl_V1585h kl_V1585t
                                                                                         _ -> pat_cond_47
                                                                    case kl_if_34 of
                                                                        Atom (B (True)) -> do !appl_48 <- kl_V1585 `pseq` tl kl_V1585
                                                                                              !appl_49 <- appl_48 `pseq` hd appl_48
                                                                                              !appl_50 <- kl_V1585 `pseq` tl kl_V1585
                                                                                              !appl_51 <- appl_50 `pseq` tl appl_50
                                                                                              !appl_52 <- appl_51 `pseq` hd appl_51
                                                                                              let !appl_53 = Atom Nil
                                                                                              !appl_54 <- appl_53 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*")) appl_53
                                                                                              !appl_55 <- appl_54 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_54
                                                                                              let !appl_56 = Atom Nil
                                                                                              !appl_57 <- appl_55 `pseq` (appl_56 `pseq` klCons appl_55 appl_56)
                                                                                              !appl_58 <- appl_52 `pseq` (appl_57 `pseq` klCons appl_52 appl_57)
                                                                                              !appl_59 <- appl_49 `pseq` (appl_58 `pseq` klCons appl_49 appl_58)
                                                                                              appl_59 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_59
                                                                        Atom (B (False)) -> do !kl_if_60 <- let pat_cond_61 kl_V1585 kl_V1585h kl_V1585t = do !kl_if_62 <- let pat_cond_63 = do !kl_if_64 <- let pat_cond_65 kl_V1585t kl_V1585th kl_V1585tt = do !kl_if_66 <- let pat_cond_67 kl_V1585tt kl_V1585tth kl_V1585ttt = do !kl_if_68 <- let pat_cond_69 kl_V1585ttt kl_V1585ttth kl_V1585tttt = do let !appl_70 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                               !kl_if_71 <- appl_70 `pseq` (kl_V1585tttt `pseq` eq appl_70 kl_V1585tttt)
                                                                                                                                                                                                                                                                                                                                                                                                               case kl_if_71 of
                                                                                                                                                                                                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                        pat_cond_72 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                     in case kl_V1585ttt of
                                                                                                                                                                                                                                                                                                                                                            !(kl_V1585ttt@(Cons (!kl_V1585ttth)
                                                                                                                                                                                                                                                                                                                                                                                (!kl_V1585tttt))) -> pat_cond_69 kl_V1585ttt kl_V1585ttth kl_V1585tttt
                                                                                                                                                                                                                                                                                                                                                            _ -> pat_cond_72
                                                                                                                                                                                                                                                                                                                                       case kl_if_68 of
                                                                                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                   pat_cond_73 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                in case kl_V1585tt of
                                                                                                                                                                                                                                                                                       !(kl_V1585tt@(Cons (!kl_V1585tth)
                                                                                                                                                                                                                                                                                                          (!kl_V1585ttt))) -> pat_cond_67 kl_V1585tt kl_V1585tth kl_V1585ttt
                                                                                                                                                                                                                                                                                       _ -> pat_cond_73
                                                                                                                                                                                                                                                                  case kl_if_66 of
                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                 pat_cond_74 = do do return (Atom (B False))
                                                                                                                                                                                                              in case kl_V1585t of
                                                                                                                                                                                                                     !(kl_V1585t@(Cons (!kl_V1585th)
                                                                                                                                                                                                                                       (!kl_V1585tt))) -> pat_cond_65 kl_V1585t kl_V1585th kl_V1585tt
                                                                                                                                                                                                                     _ -> pat_cond_74
                                                                                                                                                                                                case kl_if_64 of
                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                               pat_cond_75 = do do return (Atom (B False))
                                                                                                                                                                            in case kl_V1585h of
                                                                                                                                                                                   kl_V1585h@(Atom (UnboundSym "get/or")) -> pat_cond_63
                                                                                                                                                                                   kl_V1585h@(ApplC (PL "get/or"
                                                                                                                                                                                                        _)) -> pat_cond_63
                                                                                                                                                                                   kl_V1585h@(ApplC (Func "get/or"
                                                                                                                                                                                                          _)) -> pat_cond_63
                                                                                                                                                                                   _ -> pat_cond_75
                                                                                                                                                              case kl_if_62 of
                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                pat_cond_76 = do do return (Atom (B False))
                                                                                                             in case kl_V1585 of
                                                                                                                    !(kl_V1585@(Cons (!kl_V1585h)
                                                                                                                                     (!kl_V1585t))) -> pat_cond_61 kl_V1585 kl_V1585h kl_V1585t
                                                                                                                    _ -> pat_cond_76
                                                                                               case kl_if_60 of
                                                                                                   Atom (B (True)) -> do !appl_77 <- kl_V1585 `pseq` tl kl_V1585
                                                                                                                         !appl_78 <- appl_77 `pseq` hd appl_77
                                                                                                                         !appl_79 <- kl_V1585 `pseq` tl kl_V1585
                                                                                                                         !appl_80 <- appl_79 `pseq` tl appl_79
                                                                                                                         !appl_81 <- appl_80 `pseq` hd appl_80
                                                                                                                         !appl_82 <- kl_V1585 `pseq` tl kl_V1585
                                                                                                                         !appl_83 <- appl_82 `pseq` tl appl_82
                                                                                                                         !appl_84 <- appl_83 `pseq` tl appl_83
                                                                                                                         !appl_85 <- appl_84 `pseq` hd appl_84
                                                                                                                         let !appl_86 = Atom Nil
                                                                                                                         !appl_87 <- appl_86 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*")) appl_86
                                                                                                                         !appl_88 <- appl_87 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_87
                                                                                                                         let !appl_89 = Atom Nil
                                                                                                                         !appl_90 <- appl_88 `pseq` (appl_89 `pseq` klCons appl_88 appl_89)
                                                                                                                         !appl_91 <- appl_85 `pseq` (appl_90 `pseq` klCons appl_85 appl_90)
                                                                                                                         !appl_92 <- appl_81 `pseq` (appl_91 `pseq` klCons appl_81 appl_91)
                                                                                                                         !appl_93 <- appl_78 `pseq` (appl_92 `pseq` klCons appl_78 appl_92)
                                                                                                                         appl_93 `pseq` klCons (ApplC (wrapNamed "get/or" kl_getDivor)) appl_93
                                                                                                   Atom (B (False)) -> do !kl_if_94 <- let pat_cond_95 kl_V1585 kl_V1585h kl_V1585t = do !kl_if_96 <- let pat_cond_97 = do !kl_if_98 <- let pat_cond_99 kl_V1585t kl_V1585th kl_V1585tt = do !kl_if_100 <- let pat_cond_101 kl_V1585tt kl_V1585tth kl_V1585ttt = do let !appl_102 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                    !kl_if_103 <- appl_102 `pseq` (kl_V1585ttt `pseq` eq appl_102 kl_V1585ttt)
                                                                                                                                                                                                                                                                                                                                                                    case kl_if_103 of
                                                                                                                                                                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                               pat_cond_104 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                            in case kl_V1585tt of
                                                                                                                                                                                                                                                                                                                   !(kl_V1585tt@(Cons (!kl_V1585tth)
                                                                                                                                                                                                                                                                                                                                      (!kl_V1585ttt))) -> pat_cond_101 kl_V1585tt kl_V1585tth kl_V1585ttt
                                                                                                                                                                                                                                                                                                                   _ -> pat_cond_104
                                                                                                                                                                                                                                                                                             case kl_if_100 of
                                                                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                            pat_cond_105 = do do return (Atom (B False))
                                                                                                                                                                                                                                         in case kl_V1585t of
                                                                                                                                                                                                                                                !(kl_V1585t@(Cons (!kl_V1585th)
                                                                                                                                                                                                                                                                  (!kl_V1585tt))) -> pat_cond_99 kl_V1585t kl_V1585th kl_V1585tt
                                                                                                                                                                                                                                                _ -> pat_cond_105
                                                                                                                                                                                                                           case kl_if_98 of
                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                          pat_cond_106 = do do return (Atom (B False))
                                                                                                                                                                                                       in case kl_V1585h of
                                                                                                                                                                                                              kl_V1585h@(Atom (UnboundSym "unput")) -> pat_cond_97
                                                                                                                                                                                                              kl_V1585h@(ApplC (PL "unput"
                                                                                                                                                                                                                                   _)) -> pat_cond_97
                                                                                                                                                                                                              kl_V1585h@(ApplC (Func "unput"
                                                                                                                                                                                                                                     _)) -> pat_cond_97
                                                                                                                                                                                                              _ -> pat_cond_106
                                                                                                                                                                                         case kl_if_96 of
                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                           pat_cond_107 = do do return (Atom (B False))
                                                                                                                                        in case kl_V1585 of
                                                                                                                                               !(kl_V1585@(Cons (!kl_V1585h)
                                                                                                                                                                (!kl_V1585t))) -> pat_cond_95 kl_V1585 kl_V1585h kl_V1585t
                                                                                                                                               _ -> pat_cond_107
                                                                                                                          case kl_if_94 of
                                                                                                                              Atom (B (True)) -> do !appl_108 <- kl_V1585 `pseq` tl kl_V1585
                                                                                                                                                    !appl_109 <- appl_108 `pseq` hd appl_108
                                                                                                                                                    !appl_110 <- kl_V1585 `pseq` tl kl_V1585
                                                                                                                                                    !appl_111 <- appl_110 `pseq` tl appl_110
                                                                                                                                                    !appl_112 <- appl_111 `pseq` hd appl_111
                                                                                                                                                    let !appl_113 = Atom Nil
                                                                                                                                                    !appl_114 <- appl_113 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*")) appl_113
                                                                                                                                                    !appl_115 <- appl_114 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_114
                                                                                                                                                    let !appl_116 = Atom Nil
                                                                                                                                                    !appl_117 <- appl_115 `pseq` (appl_116 `pseq` klCons appl_115 appl_116)
                                                                                                                                                    !appl_118 <- appl_112 `pseq` (appl_117 `pseq` klCons appl_112 appl_117)
                                                                                                                                                    !appl_119 <- appl_109 `pseq` (appl_118 `pseq` klCons appl_109 appl_118)
                                                                                                                                                    appl_119 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_119
                                                                                                                              Atom (B (False)) -> do do return kl_V1585
                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                   _ -> throwError "if: expected boolean"
                                                                        _ -> throwError "if: expected boolean"
                                             _ -> throwError "if: expected boolean"

kl_shen_function_macro :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_function_macro (!kl_V1587) = do !kl_if_0 <- let pat_cond_1 kl_V1587 kl_V1587h kl_V1587t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V1587t kl_V1587th kl_V1587tt = do let !appl_6 = Atom Nil
                                                                                                                                                                                                     !kl_if_7 <- appl_6 `pseq` (kl_V1587tt `pseq` eq appl_6 kl_V1587tt)
                                                                                                                                                                                                     case kl_if_7 of
                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                     pat_cond_8 = do do return (Atom (B False))
                                                                                                                                                  in case kl_V1587t of
                                                                                                                                                         !(kl_V1587t@(Cons (!kl_V1587th)
                                                                                                                                                                           (!kl_V1587tt))) -> pat_cond_5 kl_V1587t kl_V1587th kl_V1587tt
                                                                                                                                                         _ -> pat_cond_8
                                                                                                                                     case kl_if_4 of
                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                     pat_cond_9 = do do return (Atom (B False))
                                                                                                                  in case kl_V1587h of
                                                                                                                         kl_V1587h@(Atom (UnboundSym "function")) -> pat_cond_3
                                                                                                                         kl_V1587h@(ApplC (PL "function"
                                                                                                                                              _)) -> pat_cond_3
                                                                                                                         kl_V1587h@(ApplC (Func "function"
                                                                                                                                                _)) -> pat_cond_3
                                                                                                                         _ -> pat_cond_9
                                                                                                     case kl_if_2 of
                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                         _ -> throwError "if: expected boolean"
                                                        pat_cond_10 = do do return (Atom (B False))
                                                     in case kl_V1587 of
                                                            !(kl_V1587@(Cons (!kl_V1587h)
                                                                             (!kl_V1587t))) -> pat_cond_1 kl_V1587 kl_V1587h kl_V1587t
                                                            _ -> pat_cond_10
                                        case kl_if_0 of
                                            Atom (B (True)) -> do !appl_11 <- kl_V1587 `pseq` tl kl_V1587
                                                                  !appl_12 <- appl_11 `pseq` hd appl_11
                                                                  !appl_13 <- kl_V1587 `pseq` tl kl_V1587
                                                                  !appl_14 <- appl_13 `pseq` hd appl_13
                                                                  let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "arity")
                                                                  !appl_16 <- appl_14 `pseq` applyWrapper aw_15 [appl_14]
                                                                  appl_12 `pseq` (appl_16 `pseq` kl_shen_function_abstraction appl_12 appl_16)
                                            Atom (B (False)) -> do do return kl_V1587
                                            _ -> throwError "if: expected boolean"

kl_shen_function_abstraction :: Core.Types.KLValue ->
                                Core.Types.KLValue ->
                                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_function_abstraction (!kl_V1590) (!kl_V1591) = do let pat_cond_0 = do !appl_1 <- kl_V1590 `pseq` kl_shen_app kl_V1590 (Core.Types.Atom (Core.Types.Str " has no lambda form\n")) (Core.Types.Atom (Core.Types.UnboundSym "shen.a"))
                                                                              appl_1 `pseq` simpleError appl_1
                                                              pat_cond_2 = do let !appl_3 = Atom Nil
                                                                              !appl_4 <- kl_V1590 `pseq` (appl_3 `pseq` klCons kl_V1590 appl_3)
                                                                              appl_4 `pseq` klCons (ApplC (wrapNamed "function" kl_function)) appl_4
                                                              pat_cond_5 = do do let !appl_6 = Atom Nil
                                                                                 kl_V1590 `pseq` (kl_V1591 `pseq` (appl_6 `pseq` kl_shen_function_abstraction_help kl_V1590 kl_V1591 appl_6))
                                                           in case kl_V1591 of
                                                                  kl_V1591@(Atom (N (KI 0))) -> pat_cond_0
                                                                  kl_V1591@(Atom (N (KI (-1)))) -> pat_cond_2
                                                                  _ -> pat_cond_5

kl_shen_function_abstraction_help :: Core.Types.KLValue ->
                                     Core.Types.KLValue ->
                                     Core.Types.KLValue ->
                                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_function_abstraction_help (!kl_V1595) (!kl_V1596) (!kl_V1597) = do let pat_cond_0 = do kl_V1595 `pseq` (kl_V1597 `pseq` klCons kl_V1595 kl_V1597)
                                                                               pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_3 <- kl_V1596 `pseq` Primitives.subtract kl_V1596 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                              let !appl_4 = Atom Nil
                                                                                                                                                              !appl_5 <- kl_X `pseq` (appl_4 `pseq` klCons kl_X appl_4)
                                                                                                                                                              !appl_6 <- kl_V1597 `pseq` (appl_5 `pseq` kl_append kl_V1597 appl_5)
                                                                                                                                                              !appl_7 <- kl_V1595 `pseq` (appl_3 `pseq` (appl_6 `pseq` kl_shen_function_abstraction_help kl_V1595 appl_3 appl_6))
                                                                                                                                                              let !appl_8 = Atom Nil
                                                                                                                                                              !appl_9 <- appl_7 `pseq` (appl_8 `pseq` klCons appl_7 appl_8)
                                                                                                                                                              !appl_10 <- kl_X `pseq` (appl_9 `pseq` klCons kl_X appl_9)
                                                                                                                                                              appl_10 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "/.")) appl_10)))
                                                                                                  !appl_11 <- kl_gensym (Core.Types.Atom (Core.Types.UnboundSym "V"))
                                                                                                  appl_11 `pseq` applyWrapper appl_2 [appl_11]
                                                                            in case kl_V1596 of
                                                                                   kl_V1596@(Atom (N (KI 0))) -> pat_cond_0
                                                                                   _ -> pat_cond_1

kl_undefmacro :: Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_undefmacro (!kl_V1599) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_MacroReg) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Pos) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Remove1) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Remove2) -> do return kl_V1599)))
                                                                                                                                                                                                                                  !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*macros*"))
                                                                                                                                                                                                                                  !appl_5 <- kl_Pos `pseq` (appl_4 `pseq` kl_shen_remove_nth kl_Pos appl_4)
                                                                                                                                                                                                                                  !appl_6 <- appl_5 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "*macros*")) appl_5
                                                                                                                                                                                                                                  appl_6 `pseq` applyWrapper appl_3 [appl_6])))
                                                                                                                                                                !appl_7 <- kl_V1599 `pseq` (kl_MacroReg `pseq` kl_remove kl_V1599 kl_MacroReg)
                                                                                                                                                                !appl_8 <- appl_7 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*macroreg*")) appl_7
                                                                                                                                                                appl_8 `pseq` applyWrapper appl_2 [appl_8])))
                                                                                                  !appl_9 <- kl_V1599 `pseq` (kl_MacroReg `pseq` kl_shen_findpos kl_V1599 kl_MacroReg)
                                                                                                  appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                               !appl_10 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*macroreg*"))
                               appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_findpos :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_findpos (!kl_V1609) (!kl_V1610) = do let !appl_0 = Atom Nil
                                             !kl_if_1 <- appl_0 `pseq` (kl_V1610 `pseq` eq appl_0 kl_V1610)
                                             case kl_if_1 of
                                                 Atom (B (True)) -> do !appl_2 <- kl_V1609 `pseq` kl_shen_app kl_V1609 (Core.Types.Atom (Core.Types.Str " is not a macro\n")) (Core.Types.Atom (Core.Types.UnboundSym "shen.a"))
                                                                       appl_2 `pseq` simpleError appl_2
                                                 Atom (B (False)) -> do let pat_cond_3 kl_V1610 kl_V1610h kl_V1610t = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                            pat_cond_4 kl_V1610 kl_V1610h kl_V1610t = do !appl_5 <- kl_V1609 `pseq` (kl_V1610t `pseq` kl_shen_findpos kl_V1609 kl_V1610t)
                                                                                                                         appl_5 `pseq` add (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_5
                                                                            pat_cond_6 = do do kl_shen_f_error (ApplC (wrapNamed "shen.findpos" kl_shen_findpos))
                                                                         in case kl_V1610 of
                                                                                !(kl_V1610@(Cons (!kl_V1610h)
                                                                                                 (!kl_V1610t))) | eqCore kl_V1610h kl_V1609 -> pat_cond_3 kl_V1610 kl_V1610h kl_V1610t
                                                                                !(kl_V1610@(Cons (!kl_V1610h)
                                                                                                 (!kl_V1610t))) -> pat_cond_4 kl_V1610 kl_V1610h kl_V1610t
                                                                                _ -> pat_cond_6
                                                 _ -> throwError "if: expected boolean"

kl_shen_remove_nth :: Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_remove_nth (!kl_V1615) (!kl_V1616) = do !kl_if_0 <- let pat_cond_1 = do let pat_cond_2 kl_V1616 kl_V1616h kl_V1616t = do return (Atom (B True))
                                                                                    pat_cond_3 = do do return (Atom (B False))
                                                                                 in case kl_V1616 of
                                                                                        !(kl_V1616@(Cons (!kl_V1616h)
                                                                                                         (!kl_V1616t))) -> pat_cond_2 kl_V1616 kl_V1616h kl_V1616t
                                                                                        _ -> pat_cond_3
                                                                pat_cond_4 = do do return (Atom (B False))
                                                             in case kl_V1615 of
                                                                    kl_V1615@(Atom (N (KI 1))) -> pat_cond_1
                                                                    _ -> pat_cond_4
                                                case kl_if_0 of
                                                    Atom (B (True)) -> do kl_V1616 `pseq` tl kl_V1616
                                                    Atom (B (False)) -> do let pat_cond_5 kl_V1616 kl_V1616h kl_V1616t = do !appl_6 <- kl_V1615 `pseq` Primitives.subtract kl_V1615 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                            !appl_7 <- appl_6 `pseq` (kl_V1616t `pseq` kl_shen_remove_nth appl_6 kl_V1616t)
                                                                                                                            kl_V1616h `pseq` (appl_7 `pseq` klCons kl_V1616h appl_7)
                                                                               pat_cond_8 = do do kl_shen_f_error (ApplC (wrapNamed "shen.remove-nth" kl_shen_remove_nth))
                                                                            in case kl_V1616 of
                                                                                   !(kl_V1616@(Cons (!kl_V1616h)
                                                                                                    (!kl_V1616t))) -> pat_cond_5 kl_V1616 kl_V1616h kl_V1616t
                                                                                   _ -> pat_cond_8
                                                    _ -> throwError "if: expected boolean"

expr10 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr10 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
