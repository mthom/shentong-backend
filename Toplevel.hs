{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Toplevel where

import Control.Monad.Except
import Control.Parallel
import Environment
import Core.Primitives as Primitives
import Backend.Utils
import Core.Types
import Core.Utils
import Wrap

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

kl_shen_shen :: Core.Types.KLContext Core.Types.Env
                                     Core.Types.KLValue
kl_shen_shen = do !appl_0 <- kl_shen_credits
                  !appl_1 <- kl_shen_loop
                  let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "do")
                  appl_0 `pseq` (appl_1 `pseq` applyWrapper aw_2 [appl_0, appl_1])

kl_exit :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_exit (!kl_V3800) = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*continue-repl-loop*")) (Atom (B False))

kl_shen_loop :: Core.Types.KLContext Core.Types.Env
                                     Core.Types.KLValue
kl_shen_loop = do !appl_0 <- kl_shen_initialise_environment
                  !appl_1 <- kl_shen_prompt
                  !appl_2 <- (do kl_shen_read_evaluate_print) `catchError` (\(!kl_E) -> do !appl_3 <- kl_E `pseq` errorToString (Excep kl_E)
                                                                                           let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                                                                                           !appl_5 <- applyWrapper aw_4 []
                                                                                           let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "pr")
                                                                                           appl_3 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_3,
                                                                                                                                           appl_5]))
                  !kl_if_7 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*continue-repl-loop*"))
                  !appl_8 <- case kl_if_7 of
                                 Atom (B (True)) -> do kl_shen_loop
                                 Atom (B (False)) -> do do return (ApplC (wrapNamed "exit" kl_exit))
                                 _ -> throwError "if: expected boolean"
                  let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "do")
                  !appl_10 <- appl_2 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_2,
                                                                              appl_8])
                  let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "do")
                  !appl_12 <- appl_1 `pseq` (appl_10 `pseq` applyWrapper aw_11 [appl_1,
                                                                                appl_10])
                  let !aw_13 = Core.Types.Atom (Core.Types.UnboundSym "do")
                  appl_0 `pseq` (appl_12 `pseq` applyWrapper aw_13 [appl_0, appl_12])

kl_shen_credits :: Core.Types.KLContext Core.Types.Env
                                        Core.Types.KLValue
kl_shen_credits = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                     !appl_1 <- applyWrapper aw_0 []
                     let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                     !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [Core.Types.Atom (Core.Types.Str "\nShen, copyright (C) 2010-2015 Mark Tarver\n"),
                                                                 appl_1]
                     !appl_4 <- value (Core.Types.Atom (Core.Types.UnboundSym "*version*"))
                     let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                     !appl_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4,
                                                                 Core.Types.Atom (Core.Types.Str "\n"),
                                                                 Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                     !appl_7 <- appl_6 `pseq` cn (Core.Types.Atom (Core.Types.Str "www.shenlanguage.org, ")) appl_6
                     let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                     !appl_9 <- applyWrapper aw_8 []
                     let !aw_10 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                     !appl_11 <- appl_7 `pseq` (appl_9 `pseq` applyWrapper aw_10 [appl_7,
                                                                                  appl_9])
                     !appl_12 <- value (Core.Types.Atom (Core.Types.UnboundSym "*language*"))
                     !appl_13 <- value (Core.Types.Atom (Core.Types.UnboundSym "*implementation*"))
                     let !aw_14 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                     !appl_15 <- appl_13 `pseq` applyWrapper aw_14 [appl_13,
                                                                    Core.Types.Atom (Core.Types.Str ""),
                                                                    Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                     !appl_16 <- appl_15 `pseq` cn (Core.Types.Atom (Core.Types.Str ", implementation: ")) appl_15
                     let !aw_17 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                     !appl_18 <- appl_12 `pseq` (appl_16 `pseq` applyWrapper aw_17 [appl_12,
                                                                                    appl_16,
                                                                                    Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                     !appl_19 <- appl_18 `pseq` cn (Core.Types.Atom (Core.Types.Str "running under ")) appl_18
                     let !aw_20 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                     !appl_21 <- applyWrapper aw_20 []
                     let !aw_22 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                     !appl_23 <- appl_19 `pseq` (appl_21 `pseq` applyWrapper aw_22 [appl_19,
                                                                                    appl_21])
                     !appl_24 <- value (Core.Types.Atom (Core.Types.UnboundSym "*port*"))
                     !appl_25 <- value (Core.Types.Atom (Core.Types.UnboundSym "*porters*"))
                     let !aw_26 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                     !appl_27 <- appl_25 `pseq` applyWrapper aw_26 [appl_25,
                                                                    Core.Types.Atom (Core.Types.Str "\n"),
                                                                    Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                     !appl_28 <- appl_27 `pseq` cn (Core.Types.Atom (Core.Types.Str " ported by ")) appl_27
                     let !aw_29 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                     !appl_30 <- appl_24 `pseq` (appl_28 `pseq` applyWrapper aw_29 [appl_24,
                                                                                    appl_28,
                                                                                    Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                     !appl_31 <- appl_30 `pseq` cn (Core.Types.Atom (Core.Types.Str "\nport ")) appl_30
                     let !aw_32 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                     !appl_33 <- applyWrapper aw_32 []
                     let !aw_34 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                     !appl_35 <- appl_31 `pseq` (appl_33 `pseq` applyWrapper aw_34 [appl_31,
                                                                                    appl_33])
                     let !aw_36 = Core.Types.Atom (Core.Types.UnboundSym "do")
                     !appl_37 <- appl_23 `pseq` (appl_35 `pseq` applyWrapper aw_36 [appl_23,
                                                                                    appl_35])
                     let !aw_38 = Core.Types.Atom (Core.Types.UnboundSym "do")
                     !appl_39 <- appl_11 `pseq` (appl_37 `pseq` applyWrapper aw_38 [appl_11,
                                                                                    appl_37])
                     let !aw_40 = Core.Types.Atom (Core.Types.UnboundSym "do")
                     appl_3 `pseq` (appl_39 `pseq` applyWrapper aw_40 [appl_3, appl_39])

kl_shen_initialise_environment :: Core.Types.KLContext Core.Types.Env
                                                       Core.Types.KLValue
kl_shen_initialise_environment = do let !appl_0 = Atom Nil
                                    !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_0
                                    !appl_2 <- appl_1 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*catch*")) appl_1
                                    !appl_3 <- appl_2 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_2
                                    !appl_4 <- appl_3 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*process-counter*")) appl_3
                                    !appl_5 <- appl_4 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_4
                                    !appl_6 <- appl_5 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*infs*")) appl_5
                                    !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) appl_6
                                    !appl_8 <- appl_7 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_7
                                    appl_8 `pseq` kl_shen_multiple_set appl_8

kl_shen_multiple_set :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_multiple_set (!kl_V3802) = do let !appl_0 = Atom Nil
                                      !kl_if_1 <- appl_0 `pseq` (kl_V3802 `pseq` eq appl_0 kl_V3802)
                                      case kl_if_1 of
                                          Atom (B (True)) -> do return (Atom Nil)
                                          Atom (B (False)) -> do let pat_cond_2 kl_V3802 kl_V3802h kl_V3802t kl_V3802th kl_V3802tt = do !appl_3 <- kl_V3802h `pseq` (kl_V3802th `pseq` klSet kl_V3802h kl_V3802th)
                                                                                                                                        !appl_4 <- kl_V3802tt `pseq` kl_shen_multiple_set kl_V3802tt
                                                                                                                                        let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                                                                                                                        appl_3 `pseq` (appl_4 `pseq` applyWrapper aw_5 [appl_3,
                                                                                                                                                                                        appl_4])
                                                                     pat_cond_6 = do do let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                        applyWrapper aw_7 [ApplC (wrapNamed "shen.multiple-set" kl_shen_multiple_set)]
                                                                  in case kl_V3802 of
                                                                         !(kl_V3802@(Cons (!kl_V3802h)
                                                                                          (!(kl_V3802t@(Cons (!kl_V3802th)
                                                                                                             (!kl_V3802tt)))))) -> pat_cond_2 kl_V3802 kl_V3802h kl_V3802t kl_V3802th kl_V3802tt
                                                                         _ -> pat_cond_6
                                          _ -> throwError "if: expected boolean"

kl_destroy :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_destroy (!kl_V3804) = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "declare")
                            kl_V3804 `pseq` applyWrapper aw_0 [kl_V3804,
                                                               Core.Types.Atom (Core.Types.UnboundSym "symbol")]

kl_shen_read_evaluate_print :: Core.Types.KLContext Core.Types.Env
                                                    Core.Types.KLValue
kl_shen_read_evaluate_print = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Lineread) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_History) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_NewLineread) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_NewHistory) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parsed) -> do kl_Parsed `pseq` kl_shen_toplevel kl_Parsed)))
                                                                                                                                                                                                                                                                                                                 let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "fst")
                                                                                                                                                                                                                                                                                                                 !appl_6 <- kl_NewLineread `pseq` applyWrapper aw_5 [kl_NewLineread]
                                                                                                                                                                                                                                                                                                                 appl_6 `pseq` applyWrapper appl_4 [appl_6])))
                                                                                                                                                                                                                                            !appl_7 <- kl_NewLineread `pseq` (kl_History `pseq` kl_shen_update_history kl_NewLineread kl_History)
                                                                                                                                                                                                                                            appl_7 `pseq` applyWrapper appl_3 [appl_7])))
                                                                                                                                                                      !appl_8 <- kl_Lineread `pseq` (kl_History `pseq` kl_shen_retrieve_from_history_if_needed kl_Lineread kl_History)
                                                                                                                                                                      appl_8 `pseq` applyWrapper appl_2 [appl_8])))
                                                                                                    !appl_9 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*history*"))
                                                                                                    appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                                 !appl_10 <- kl_shen_toplineread
                                 appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_retrieve_from_history_if_needed :: Core.Types.KLValue ->
                                           Core.Types.KLValue ->
                                           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_retrieve_from_history_if_needed (!kl_V3816) (!kl_V3817) = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "tuple?")
                                                                     !kl_if_1 <- kl_V3816 `pseq` applyWrapper aw_0 [kl_V3816]
                                                                     !kl_if_2 <- case kl_if_1 of
                                                                                     Atom (B (True)) -> do let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                           !appl_4 <- kl_V3816 `pseq` applyWrapper aw_3 [kl_V3816]
                                                                                                           !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                           !kl_if_6 <- case kl_if_5 of
                                                                                                                           Atom (B (True)) -> do let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                 !appl_8 <- kl_V3816 `pseq` applyWrapper aw_7 [kl_V3816]
                                                                                                                                                 !appl_9 <- appl_8 `pseq` hd appl_8
                                                                                                                                                 !appl_10 <- kl_shen_space
                                                                                                                                                 !appl_11 <- kl_shen_newline
                                                                                                                                                 let !appl_12 = Atom Nil
                                                                                                                                                 !appl_13 <- appl_11 `pseq` (appl_12 `pseq` klCons appl_11 appl_12)
                                                                                                                                                 !appl_14 <- appl_10 `pseq` (appl_13 `pseq` klCons appl_10 appl_13)
                                                                                                                                                 let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "element?")
                                                                                                                                                 !kl_if_16 <- appl_9 `pseq` (appl_14 `pseq` applyWrapper aw_15 [appl_9,
                                                                                                                                                                                                                appl_14])
                                                                                                                                                 case kl_if_16 of
                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                           case kl_if_6 of
                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                               _ -> throwError "if: expected boolean"
                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                     _ -> throwError "if: expected boolean"
                                                                     case kl_if_2 of
                                                                         Atom (B (True)) -> do let !aw_17 = Core.Types.Atom (Core.Types.UnboundSym "fst")
                                                                                               !appl_18 <- kl_V3816 `pseq` applyWrapper aw_17 [kl_V3816]
                                                                                               let !aw_19 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                               !appl_20 <- kl_V3816 `pseq` applyWrapper aw_19 [kl_V3816]
                                                                                               !appl_21 <- appl_20 `pseq` tl appl_20
                                                                                               let !aw_22 = Core.Types.Atom (Core.Types.UnboundSym "@p")
                                                                                               !appl_23 <- appl_18 `pseq` (appl_21 `pseq` applyWrapper aw_22 [appl_18,
                                                                                                                                                              appl_21])
                                                                                               appl_23 `pseq` (kl_V3817 `pseq` kl_shen_retrieve_from_history_if_needed appl_23 kl_V3817)
                                                                         Atom (B (False)) -> do let !aw_24 = Core.Types.Atom (Core.Types.UnboundSym "tuple?")
                                                                                                !kl_if_25 <- kl_V3816 `pseq` applyWrapper aw_24 [kl_V3816]
                                                                                                !kl_if_26 <- case kl_if_25 of
                                                                                                                 Atom (B (True)) -> do let !aw_27 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                       !appl_28 <- kl_V3816 `pseq` applyWrapper aw_27 [kl_V3816]
                                                                                                                                       !kl_if_29 <- appl_28 `pseq` consP appl_28
                                                                                                                                       !kl_if_30 <- case kl_if_29 of
                                                                                                                                                        Atom (B (True)) -> do let !aw_31 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                              !appl_32 <- kl_V3816 `pseq` applyWrapper aw_31 [kl_V3816]
                                                                                                                                                                              !appl_33 <- appl_32 `pseq` tl appl_32
                                                                                                                                                                              !kl_if_34 <- appl_33 `pseq` consP appl_33
                                                                                                                                                                              !kl_if_35 <- case kl_if_34 of
                                                                                                                                                                                               Atom (B (True)) -> do let !appl_36 = Atom Nil
                                                                                                                                                                                                                     let !aw_37 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                     !appl_38 <- kl_V3816 `pseq` applyWrapper aw_37 [kl_V3816]
                                                                                                                                                                                                                     !appl_39 <- appl_38 `pseq` tl appl_38
                                                                                                                                                                                                                     !appl_40 <- appl_39 `pseq` tl appl_39
                                                                                                                                                                                                                     !kl_if_41 <- appl_36 `pseq` (appl_40 `pseq` eq appl_36 appl_40)
                                                                                                                                                                                                                     !kl_if_42 <- case kl_if_41 of
                                                                                                                                                                                                                                      Atom (B (True)) -> do !kl_if_43 <- let pat_cond_44 kl_V3817 kl_V3817h kl_V3817t = do let !aw_45 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                           !appl_46 <- kl_V3816 `pseq` applyWrapper aw_45 [kl_V3816]
                                                                                                                                                                                                                                                                                                                           !appl_47 <- appl_46 `pseq` hd appl_46
                                                                                                                                                                                                                                                                                                                           !appl_48 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                                                           !kl_if_49 <- appl_47 `pseq` (appl_48 `pseq` eq appl_47 appl_48)
                                                                                                                                                                                                                                                                                                                           !kl_if_50 <- case kl_if_49 of
                                                                                                                                                                                                                                                                                                                                            Atom (B (True)) -> do let !aw_51 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                  !appl_52 <- kl_V3816 `pseq` applyWrapper aw_51 [kl_V3816]
                                                                                                                                                                                                                                                                                                                                                                  !appl_53 <- appl_52 `pseq` tl appl_52
                                                                                                                                                                                                                                                                                                                                                                  !appl_54 <- appl_53 `pseq` hd appl_53
                                                                                                                                                                                                                                                                                                                                                                  !appl_55 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                                                                                                  !kl_if_56 <- appl_54 `pseq` (appl_55 `pseq` eq appl_54 appl_55)
                                                                                                                                                                                                                                                                                                                                                                  case kl_if_56 of
                                                                                                                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                           case kl_if_50 of
                                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                             pat_cond_57 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                          in case kl_V3817 of
                                                                                                                                                                                                                                                                                 !(kl_V3817@(Cons (!kl_V3817h)
                                                                                                                                                                                                                                                                                                  (!kl_V3817t))) -> pat_cond_44 kl_V3817 kl_V3817h kl_V3817t
                                                                                                                                                                                                                                                                                 _ -> pat_cond_57
                                                                                                                                                                                                                                                            case kl_if_43 of
                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                     case kl_if_42 of
                                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                              case kl_if_35 of
                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                       case kl_if_30 of
                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                case kl_if_26 of
                                                                                                    Atom (B (True)) -> do let !appl_58 = ApplC (Func "lambda" (Context (\(!kl_PastPrint) -> do kl_V3817 `pseq` hd kl_V3817)))
                                                                                                                          !appl_59 <- kl_V3817 `pseq` hd kl_V3817
                                                                                                                          let !aw_60 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                          !appl_61 <- appl_59 `pseq` applyWrapper aw_60 [appl_59]
                                                                                                                          !appl_62 <- appl_61 `pseq` kl_shen_prbytes appl_61
                                                                                                                          appl_62 `pseq` applyWrapper appl_58 [appl_62]
                                                                                                    Atom (B (False)) -> do let !aw_63 = Core.Types.Atom (Core.Types.UnboundSym "tuple?")
                                                                                                                           !kl_if_64 <- kl_V3816 `pseq` applyWrapper aw_63 [kl_V3816]
                                                                                                                           !kl_if_65 <- case kl_if_64 of
                                                                                                                                            Atom (B (True)) -> do let !aw_66 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                  !appl_67 <- kl_V3816 `pseq` applyWrapper aw_66 [kl_V3816]
                                                                                                                                                                  !kl_if_68 <- appl_67 `pseq` consP appl_67
                                                                                                                                                                  !kl_if_69 <- case kl_if_68 of
                                                                                                                                                                                   Atom (B (True)) -> do let !aw_70 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                         !appl_71 <- kl_V3816 `pseq` applyWrapper aw_70 [kl_V3816]
                                                                                                                                                                                                         !appl_72 <- appl_71 `pseq` hd appl_71
                                                                                                                                                                                                         !appl_73 <- kl_shen_exclamation
                                                                                                                                                                                                         !kl_if_74 <- appl_72 `pseq` (appl_73 `pseq` eq appl_72 appl_73)
                                                                                                                                                                                                         case kl_if_74 of
                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                  case kl_if_69 of
                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                           case kl_if_65 of
                                                                                                                               Atom (B (True)) -> do let !appl_75 = ApplC (Func "lambda" (Context (\(!kl_KeyP) -> do let !appl_76 = ApplC (Func "lambda" (Context (\(!kl_Find) -> do let !appl_77 = ApplC (Func "lambda" (Context (\(!kl_PastPrint) -> do return kl_Find)))
                                                                                                                                                                                                                                                                                     let !aw_78 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                     !appl_79 <- kl_Find `pseq` applyWrapper aw_78 [kl_Find]
                                                                                                                                                                                                                                                                                     !appl_80 <- appl_79 `pseq` kl_shen_prbytes appl_79
                                                                                                                                                                                                                                                                                     appl_80 `pseq` applyWrapper appl_77 [appl_80])))
                                                                                                                                                                                                                     !appl_81 <- kl_KeyP `pseq` (kl_V3817 `pseq` kl_shen_find_past_inputs kl_KeyP kl_V3817)
                                                                                                                                                                                                                     let !aw_82 = Core.Types.Atom (Core.Types.UnboundSym "head")
                                                                                                                                                                                                                     !appl_83 <- appl_81 `pseq` applyWrapper aw_82 [appl_81]
                                                                                                                                                                                                                     appl_83 `pseq` applyWrapper appl_76 [appl_83])))
                                                                                                                                                     let !aw_84 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                     !appl_85 <- kl_V3816 `pseq` applyWrapper aw_84 [kl_V3816]
                                                                                                                                                     !appl_86 <- appl_85 `pseq` tl appl_85
                                                                                                                                                     !appl_87 <- appl_86 `pseq` (kl_V3817 `pseq` kl_shen_make_key appl_86 kl_V3817)
                                                                                                                                                     appl_87 `pseq` applyWrapper appl_75 [appl_87]
                                                                                                                               Atom (B (False)) -> do let !aw_88 = Core.Types.Atom (Core.Types.UnboundSym "tuple?")
                                                                                                                                                      !kl_if_89 <- kl_V3816 `pseq` applyWrapper aw_88 [kl_V3816]
                                                                                                                                                      !kl_if_90 <- case kl_if_89 of
                                                                                                                                                                       Atom (B (True)) -> do let !aw_91 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                             !appl_92 <- kl_V3816 `pseq` applyWrapper aw_91 [kl_V3816]
                                                                                                                                                                                             !kl_if_93 <- appl_92 `pseq` consP appl_92
                                                                                                                                                                                             !kl_if_94 <- case kl_if_93 of
                                                                                                                                                                                                              Atom (B (True)) -> do let !appl_95 = Atom Nil
                                                                                                                                                                                                                                    let !aw_96 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                                    !appl_97 <- kl_V3816 `pseq` applyWrapper aw_96 [kl_V3816]
                                                                                                                                                                                                                                    !appl_98 <- appl_97 `pseq` tl appl_97
                                                                                                                                                                                                                                    !kl_if_99 <- appl_95 `pseq` (appl_98 `pseq` eq appl_95 appl_98)
                                                                                                                                                                                                                                    !kl_if_100 <- case kl_if_99 of
                                                                                                                                                                                                                                                      Atom (B (True)) -> do let !aw_101 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                            !appl_102 <- kl_V3816 `pseq` applyWrapper aw_101 [kl_V3816]
                                                                                                                                                                                                                                                                            !appl_103 <- appl_102 `pseq` hd appl_102
                                                                                                                                                                                                                                                                            !appl_104 <- kl_shen_percent
                                                                                                                                                                                                                                                                            !kl_if_105 <- appl_103 `pseq` (appl_104 `pseq` eq appl_103 appl_104)
                                                                                                                                                                                                                                                                            case kl_if_105 of
                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                    case kl_if_100 of
                                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                                                                             case kl_if_94 of
                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                      case kl_if_90 of
                                                                                                                                                          Atom (B (True)) -> do let !appl_106 = ApplC (Func "lambda" (Context (\(!kl_X) -> do return (Atom (B True)))))
                                                                                                                                                                                let !aw_107 = Core.Types.Atom (Core.Types.UnboundSym "reverse")
                                                                                                                                                                                !appl_108 <- kl_V3817 `pseq` applyWrapper aw_107 [kl_V3817]
                                                                                                                                                                                !appl_109 <- appl_106 `pseq` (appl_108 `pseq` kl_shen_print_past_inputs appl_106 appl_108 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))))
                                                                                                                                                                                let !aw_110 = Core.Types.Atom (Core.Types.UnboundSym "abort")
                                                                                                                                                                                !appl_111 <- applyWrapper aw_110 []
                                                                                                                                                                                let !aw_112 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                                                                                                                                                                appl_109 `pseq` (appl_111 `pseq` applyWrapper aw_112 [appl_109,
                                                                                                                                                                                                                                      appl_111])
                                                                                                                                                          Atom (B (False)) -> do let !aw_113 = Core.Types.Atom (Core.Types.UnboundSym "tuple?")
                                                                                                                                                                                 !kl_if_114 <- kl_V3816 `pseq` applyWrapper aw_113 [kl_V3816]
                                                                                                                                                                                 !kl_if_115 <- case kl_if_114 of
                                                                                                                                                                                                   Atom (B (True)) -> do let !aw_116 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                         !appl_117 <- kl_V3816 `pseq` applyWrapper aw_116 [kl_V3816]
                                                                                                                                                                                                                         !kl_if_118 <- appl_117 `pseq` consP appl_117
                                                                                                                                                                                                                         !kl_if_119 <- case kl_if_118 of
                                                                                                                                                                                                                                           Atom (B (True)) -> do let !aw_120 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                 !appl_121 <- kl_V3816 `pseq` applyWrapper aw_120 [kl_V3816]
                                                                                                                                                                                                                                                                 !appl_122 <- appl_121 `pseq` hd appl_121
                                                                                                                                                                                                                                                                 !appl_123 <- kl_shen_percent
                                                                                                                                                                                                                                                                 !kl_if_124 <- appl_122 `pseq` (appl_123 `pseq` eq appl_122 appl_123)
                                                                                                                                                                                                                                                                 case kl_if_124 of
                                                                                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                         case kl_if_119 of
                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                 case kl_if_115 of
                                                                                                                                                                                     Atom (B (True)) -> do let !appl_125 = ApplC (Func "lambda" (Context (\(!kl_KeyP) -> do let !appl_126 = ApplC (Func "lambda" (Context (\(!kl_Pastprint) -> do let !aw_127 = Core.Types.Atom (Core.Types.UnboundSym "abort")
                                                                                                                                                                                                                                                                                                                                                  applyWrapper aw_127 [])))
                                                                                                                                                                                                                                                                            let !aw_128 = Core.Types.Atom (Core.Types.UnboundSym "reverse")
                                                                                                                                                                                                                                                                            !appl_129 <- kl_V3817 `pseq` applyWrapper aw_128 [kl_V3817]
                                                                                                                                                                                                                                                                            !appl_130 <- kl_KeyP `pseq` (appl_129 `pseq` kl_shen_print_past_inputs kl_KeyP appl_129 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))))
                                                                                                                                                                                                                                                                            appl_130 `pseq` applyWrapper appl_126 [appl_130])))
                                                                                                                                                                                                           let !aw_131 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                           !appl_132 <- kl_V3816 `pseq` applyWrapper aw_131 [kl_V3816]
                                                                                                                                                                                                           !appl_133 <- appl_132 `pseq` tl appl_132
                                                                                                                                                                                                           !appl_134 <- appl_133 `pseq` (kl_V3817 `pseq` kl_shen_make_key appl_133 kl_V3817)
                                                                                                                                                                                                           appl_134 `pseq` applyWrapper appl_125 [appl_134]
                                                                                                                                                                                     Atom (B (False)) -> do do return kl_V3816
                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                    _ -> throwError "if: expected boolean"
                                                                         _ -> throwError "if: expected boolean"

kl_shen_percent :: Core.Types.KLContext Core.Types.Env
                                        Core.Types.KLValue
kl_shen_percent = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 37)))

kl_shen_exclamation :: Core.Types.KLContext Core.Types.Env
                                            Core.Types.KLValue
kl_shen_exclamation = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 33)))

kl_shen_prbytes :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_prbytes (!kl_V3819) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Byte) -> do !appl_1 <- kl_Byte `pseq` nToString kl_Byte
                                                                                                let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                                                                                                !appl_3 <- applyWrapper aw_2 []
                                                                                                let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "pr")
                                                                                                appl_1 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_1,
                                                                                                                                                appl_3]))))
                                 let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "for-each")
                                 !appl_6 <- appl_0 `pseq` (kl_V3819 `pseq` applyWrapper aw_5 [appl_0,
                                                                                              kl_V3819])
                                 let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "nl")
                                 !appl_8 <- applyWrapper aw_7 [Core.Types.Atom (Core.Types.N (Core.Types.KI 1))]
                                 let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                 appl_6 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_6, appl_8])

kl_shen_update_history :: Core.Types.KLValue ->
                          Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_update_history (!kl_V3822) (!kl_V3823) = do !appl_0 <- kl_V3822 `pseq` (kl_V3823 `pseq` klCons kl_V3822 kl_V3823)
                                                    appl_0 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*history*")) appl_0

kl_shen_toplineread :: Core.Types.KLContext Core.Types.Env
                                            Core.Types.KLValue
kl_shen_toplineread = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "stinput")
                         !appl_1 <- applyWrapper aw_0 []
                         let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "read-char-code")
                         !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [appl_1]
                         let !appl_4 = Atom Nil
                         appl_3 `pseq` (appl_4 `pseq` kl_shen_toplineread_loop appl_3 appl_4)

kl_shen_toplineread_loop :: Core.Types.KLValue ->
                            Core.Types.KLValue ->
                            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_toplineread_loop (!kl_V3827) (!kl_V3828) = do !kl_if_0 <- let pat_cond_1 = do let !appl_2 = Atom Nil
                                                                                      !kl_if_3 <- appl_2 `pseq` (kl_V3828 `pseq` eq appl_2 kl_V3828)
                                                                                      case kl_if_3 of
                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                          _ -> throwError "if: expected boolean"
                                                                      pat_cond_4 = do do return (Atom (B False))
                                                                   in case kl_V3827 of
                                                                          kl_V3827@(Atom (N (KI (-1)))) -> pat_cond_1
                                                                          _ -> pat_cond_4
                                                      case kl_if_0 of
                                                          Atom (B (True)) -> do kl_exit (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                          Atom (B (False)) -> do !appl_5 <- kl_shen_hat
                                                                                 !kl_if_6 <- kl_V3827 `pseq` (appl_5 `pseq` eq kl_V3827 appl_5)
                                                                                 case kl_if_6 of
                                                                                     Atom (B (True)) -> do simpleError (Core.Types.Atom (Core.Types.Str "line read aborted"))
                                                                                     Atom (B (False)) -> do !appl_7 <- kl_shen_newline
                                                                                                            !appl_8 <- kl_shen_carriage_return
                                                                                                            let !appl_9 = Atom Nil
                                                                                                            !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                                                                            !appl_11 <- appl_7 `pseq` (appl_10 `pseq` klCons appl_7 appl_10)
                                                                                                            let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "element?")
                                                                                                            !kl_if_13 <- kl_V3827 `pseq` (appl_11 `pseq` applyWrapper aw_12 [kl_V3827,
                                                                                                                                                                             appl_11])
                                                                                                            case kl_if_13 of
                                                                                                                Atom (B (True)) -> do let !appl_14 = ApplC (Func "lambda" (Context (\(!kl_Line) -> do let !appl_15 = ApplC (Func "lambda" (Context (\(!kl_It) -> do !kl_if_16 <- let pat_cond_17 = do return (Atom (B True))
                                                                                                                                                                                                                                                                                     pat_cond_18 = do do let !aw_19 = Core.Types.Atom (Core.Types.UnboundSym "empty?")
                                                                                                                                                                                                                                                                                                         !kl_if_20 <- kl_Line `pseq` applyWrapper aw_19 [kl_Line]
                                                                                                                                                                                                                                                                                                         case kl_if_20 of
                                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                  in case kl_Line of
                                                                                                                                                                                                                                                                                         kl_Line@(Atom (UnboundSym "shen.nextline")) -> pat_cond_17
                                                                                                                                                                                                                                                                                         kl_Line@(ApplC (PL "shen.nextline"
                                                                                                                                                                                                                                                                                                            _)) -> pat_cond_17
                                                                                                                                                                                                                                                                                         kl_Line@(ApplC (Func "shen.nextline"
                                                                                                                                                                                                                                                                                                              _)) -> pat_cond_17
                                                                                                                                                                                                                                                                                         _ -> pat_cond_18
                                                                                                                                                                                                                                                                    case kl_if_16 of
                                                                                                                                                                                                                                                                        Atom (B (True)) -> do let !aw_21 = Core.Types.Atom (Core.Types.UnboundSym "stinput")
                                                                                                                                                                                                                                                                                              !appl_22 <- applyWrapper aw_21 []
                                                                                                                                                                                                                                                                                              let !aw_23 = Core.Types.Atom (Core.Types.UnboundSym "read-char-code")
                                                                                                                                                                                                                                                                                              !appl_24 <- appl_22 `pseq` applyWrapper aw_23 [appl_22]
                                                                                                                                                                                                                                                                                              let !appl_25 = Atom Nil
                                                                                                                                                                                                                                                                                              !appl_26 <- kl_V3827 `pseq` (appl_25 `pseq` klCons kl_V3827 appl_25)
                                                                                                                                                                                                                                                                                              let !aw_27 = Core.Types.Atom (Core.Types.UnboundSym "append")
                                                                                                                                                                                                                                                                                              !appl_28 <- kl_V3828 `pseq` (appl_26 `pseq` applyWrapper aw_27 [kl_V3828,
                                                                                                                                                                                                                                                                                                                                                              appl_26])
                                                                                                                                                                                                                                                                                              appl_24 `pseq` (appl_28 `pseq` kl_shen_toplineread_loop appl_24 appl_28)
                                                                                                                                                                                                                                                                        Atom (B (False)) -> do do let !aw_29 = Core.Types.Atom (Core.Types.UnboundSym "@p")
                                                                                                                                                                                                                                                                                                  kl_Line `pseq` (kl_V3828 `pseq` applyWrapper aw_29 [kl_Line,
                                                                                                                                                                                                                                                                                                                                                      kl_V3828])
                                                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean")))
                                                                                                                                                                                                      let !aw_30 = Core.Types.Atom (Core.Types.UnboundSym "shen.record-it")
                                                                                                                                                                                                      !appl_31 <- kl_V3828 `pseq` applyWrapper aw_30 [kl_V3828]
                                                                                                                                                                                                      appl_31 `pseq` applyWrapper appl_15 [appl_31])))
                                                                                                                                      let !appl_32 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_33 = Core.Types.Atom (Core.Types.UnboundSym "shen.<st_input>")
                                                                                                                                                                                                   kl_X `pseq` applyWrapper aw_33 [kl_X])))
                                                                                                                                      let !appl_34 = ApplC (Func "lambda" (Context (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.UnboundSym "shen.nextline")))))
                                                                                                                                      let !aw_35 = Core.Types.Atom (Core.Types.UnboundSym "compile")
                                                                                                                                      !appl_36 <- appl_32 `pseq` (kl_V3828 `pseq` (appl_34 `pseq` applyWrapper aw_35 [appl_32,
                                                                                                                                                                                                                      kl_V3828,
                                                                                                                                                                                                                      appl_34]))
                                                                                                                                      appl_36 `pseq` applyWrapper appl_14 [appl_36]
                                                                                                                Atom (B (False)) -> do do let !aw_37 = Core.Types.Atom (Core.Types.UnboundSym "stinput")
                                                                                                                                          !appl_38 <- applyWrapper aw_37 []
                                                                                                                                          let !aw_39 = Core.Types.Atom (Core.Types.UnboundSym "read-char-code")
                                                                                                                                          !appl_40 <- appl_38 `pseq` applyWrapper aw_39 [appl_38]
                                                                                                                                          !appl_41 <- let pat_cond_42 = do return kl_V3828
                                                                                                                                                          pat_cond_43 = do do let !appl_44 = Atom Nil
                                                                                                                                                                              !appl_45 <- kl_V3827 `pseq` (appl_44 `pseq` klCons kl_V3827 appl_44)
                                                                                                                                                                              let !aw_46 = Core.Types.Atom (Core.Types.UnboundSym "append")
                                                                                                                                                                              kl_V3828 `pseq` (appl_45 `pseq` applyWrapper aw_46 [kl_V3828,
                                                                                                                                                                                                                                  appl_45])
                                                                                                                                                       in case kl_V3827 of
                                                                                                                                                              kl_V3827@(Atom (N (KI (-1)))) -> pat_cond_42
                                                                                                                                                              _ -> pat_cond_43
                                                                                                                                          appl_40 `pseq` (appl_41 `pseq` kl_shen_toplineread_loop appl_40 appl_41)
                                                                                                                _ -> throwError "if: expected boolean"
                                                                                     _ -> throwError "if: expected boolean"
                                                          _ -> throwError "if: expected boolean"

kl_shen_hat :: Core.Types.KLContext Core.Types.Env
                                    Core.Types.KLValue
kl_shen_hat = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 94)))

kl_shen_newline :: Core.Types.KLContext Core.Types.Env
                                        Core.Types.KLValue
kl_shen_newline = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 10)))

kl_shen_carriage_return :: Core.Types.KLContext Core.Types.Env
                                                Core.Types.KLValue
kl_shen_carriage_return = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 13)))

kl_tc :: Core.Types.KLValue ->
         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_tc (!kl_V3834) = do let pat_cond_0 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*")) (Atom (B True))
                           pat_cond_1 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*")) (Atom (B False))
                           pat_cond_2 = do do simpleError (Core.Types.Atom (Core.Types.Str "tc expects a + or -"))
                        in case kl_V3834 of
                               kl_V3834@(Atom (UnboundSym "+")) -> pat_cond_0
                               kl_V3834@(ApplC (PL "+" _)) -> pat_cond_0
                               kl_V3834@(ApplC (Func "+" _)) -> pat_cond_0
                               kl_V3834@(Atom (UnboundSym "-")) -> pat_cond_1
                               kl_V3834@(ApplC (PL "-" _)) -> pat_cond_1
                               kl_V3834@(ApplC (Func "-" _)) -> pat_cond_1
                               _ -> pat_cond_2

kl_shen_prompt :: Core.Types.KLContext Core.Types.Env
                                       Core.Types.KLValue
kl_shen_prompt = do !kl_if_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*"))
                    case kl_if_0 of
                        Atom (B (True)) -> do !appl_1 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*history*"))
                                              let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "length")
                                              !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [appl_1]
                                              let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                              !appl_5 <- appl_3 `pseq` applyWrapper aw_4 [appl_3,
                                                                                          Core.Types.Atom (Core.Types.Str "+) "),
                                                                                          Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                              !appl_6 <- appl_5 `pseq` cn (Core.Types.Atom (Core.Types.Str "\n\n(")) appl_5
                                              let !aw_7 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                                              !appl_8 <- applyWrapper aw_7 []
                                              let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                              appl_6 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_6,
                                                                                              appl_8])
                        Atom (B (False)) -> do do !appl_10 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*history*"))
                                                  let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "length")
                                                  !appl_12 <- appl_10 `pseq` applyWrapper aw_11 [appl_10]
                                                  let !aw_13 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                  !appl_14 <- appl_12 `pseq` applyWrapper aw_13 [appl_12,
                                                                                                 Core.Types.Atom (Core.Types.Str "-) "),
                                                                                                 Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                  !appl_15 <- appl_14 `pseq` cn (Core.Types.Atom (Core.Types.Str "\n\n(")) appl_14
                                                  let !aw_16 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                                                  !appl_17 <- applyWrapper aw_16 []
                                                  let !aw_18 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                  appl_15 `pseq` (appl_17 `pseq` applyWrapper aw_18 [appl_15,
                                                                                                     appl_17])
                        _ -> throwError "if: expected boolean"

kl_shen_toplevel :: Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_toplevel (!kl_V3836) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tc*"))
                                  kl_V3836 `pseq` (appl_0 `pseq` kl_shen_toplevel_evaluate kl_V3836 appl_0)

kl_shen_find_past_inputs :: Core.Types.KLValue ->
                            Core.Types.KLValue ->
                            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_find_past_inputs (!kl_V3839) (!kl_V3840) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_F) -> do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "empty?")
                                                                                                                  !kl_if_2 <- kl_F `pseq` applyWrapper aw_1 [kl_F]
                                                                                                                  case kl_if_2 of
                                                                                                                      Atom (B (True)) -> do simpleError (Core.Types.Atom (Core.Types.Str "input not found\n"))
                                                                                                                      Atom (B (False)) -> do do return kl_F
                                                                                                                      _ -> throwError "if: expected boolean")))
                                                      !appl_3 <- kl_V3839 `pseq` (kl_V3840 `pseq` kl_shen_find kl_V3839 kl_V3840)
                                                      appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_make_key :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_make_key (!kl_V3843) (!kl_V3844) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Atom) -> do let !aw_1 = Core.Types.Atom (Core.Types.UnboundSym "integer?")
                                                                                                             !kl_if_2 <- kl_Atom `pseq` applyWrapper aw_1 [kl_Atom]
                                                                                                             case kl_if_2 of
                                                                                                                 Atom (B (True)) -> do return (ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_3 <- kl_Atom `pseq` add kl_Atom (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                                                             let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "reverse")
                                                                                                                                                                                             !appl_5 <- kl_V3844 `pseq` applyWrapper aw_4 [kl_V3844]
                                                                                                                                                                                             let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "nth")
                                                                                                                                                                                             !appl_7 <- appl_3 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_3,
                                                                                                                                                                                                                                                        appl_5])
                                                                                                                                                                                             kl_X `pseq` (appl_7 `pseq` eq kl_X appl_7)))))
                                                                                                                 Atom (B (False)) -> do do return (ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                                                                 !appl_9 <- kl_X `pseq` applyWrapper aw_8 [kl_X]
                                                                                                                                                                                                 !appl_10 <- appl_9 `pseq` kl_shen_trim_gubbins appl_9
                                                                                                                                                                                                 kl_V3843 `pseq` (appl_10 `pseq` kl_shen_prefixP kl_V3843 appl_10)))))
                                                                                                                 _ -> throwError "if: expected boolean")))
                                              let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "shen.<st_input>")
                                                                                                           kl_X `pseq` applyWrapper aw_12 [kl_X])))
                                              let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_E) -> do let pat_cond_14 kl_E kl_Eh kl_Et = do let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                 !appl_16 <- kl_E `pseq` applyWrapper aw_15 [kl_E,
                                                                                                                                                                                             Core.Types.Atom (Core.Types.Str "\n"),
                                                                                                                                                                                             Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                                                                                                                 !appl_17 <- appl_16 `pseq` cn (Core.Types.Atom (Core.Types.Str "parse error here: ")) appl_16
                                                                                                                                                 appl_17 `pseq` simpleError appl_17
                                                                                                               pat_cond_18 = do do simpleError (Core.Types.Atom (Core.Types.Str "parse error\n"))
                                                                                                            in case kl_E of
                                                                                                                   !(kl_E@(Cons (!kl_Eh)
                                                                                                                                (!kl_Et))) -> pat_cond_14 kl_E kl_Eh kl_Et
                                                                                                                   _ -> pat_cond_18)))
                                              let !aw_19 = Core.Types.Atom (Core.Types.UnboundSym "compile")
                                              !appl_20 <- appl_11 `pseq` (kl_V3843 `pseq` (appl_13 `pseq` applyWrapper aw_19 [appl_11,
                                                                                                                              kl_V3843,
                                                                                                                              appl_13]))
                                              !appl_21 <- appl_20 `pseq` hd appl_20
                                              appl_21 `pseq` applyWrapper appl_0 [appl_21]

kl_shen_trim_gubbins :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_trim_gubbins (!kl_V3846) = do !kl_if_0 <- let pat_cond_1 kl_V3846 kl_V3846h kl_V3846t = do !appl_2 <- kl_shen_space
                                                                                                   !kl_if_3 <- kl_V3846h `pseq` (appl_2 `pseq` eq kl_V3846h appl_2)
                                                                                                   case kl_if_3 of
                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                       _ -> throwError "if: expected boolean"
                                                      pat_cond_4 = do do return (Atom (B False))
                                                   in case kl_V3846 of
                                                          !(kl_V3846@(Cons (!kl_V3846h)
                                                                           (!kl_V3846t))) -> pat_cond_1 kl_V3846 kl_V3846h kl_V3846t
                                                          _ -> pat_cond_4
                                      case kl_if_0 of
                                          Atom (B (True)) -> do !appl_5 <- kl_V3846 `pseq` tl kl_V3846
                                                                appl_5 `pseq` kl_shen_trim_gubbins appl_5
                                          Atom (B (False)) -> do !kl_if_6 <- let pat_cond_7 kl_V3846 kl_V3846h kl_V3846t = do !appl_8 <- kl_shen_newline
                                                                                                                              !kl_if_9 <- kl_V3846h `pseq` (appl_8 `pseq` eq kl_V3846h appl_8)
                                                                                                                              case kl_if_9 of
                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                 pat_cond_10 = do do return (Atom (B False))
                                                                              in case kl_V3846 of
                                                                                     !(kl_V3846@(Cons (!kl_V3846h)
                                                                                                      (!kl_V3846t))) -> pat_cond_7 kl_V3846 kl_V3846h kl_V3846t
                                                                                     _ -> pat_cond_10
                                                                 case kl_if_6 of
                                                                     Atom (B (True)) -> do !appl_11 <- kl_V3846 `pseq` tl kl_V3846
                                                                                           appl_11 `pseq` kl_shen_trim_gubbins appl_11
                                                                     Atom (B (False)) -> do !kl_if_12 <- let pat_cond_13 kl_V3846 kl_V3846h kl_V3846t = do !appl_14 <- kl_shen_carriage_return
                                                                                                                                                           !kl_if_15 <- kl_V3846h `pseq` (appl_14 `pseq` eq kl_V3846h appl_14)
                                                                                                                                                           case kl_if_15 of
                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                             pat_cond_16 = do do return (Atom (B False))
                                                                                                          in case kl_V3846 of
                                                                                                                 !(kl_V3846@(Cons (!kl_V3846h)
                                                                                                                                  (!kl_V3846t))) -> pat_cond_13 kl_V3846 kl_V3846h kl_V3846t
                                                                                                                 _ -> pat_cond_16
                                                                                            case kl_if_12 of
                                                                                                Atom (B (True)) -> do !appl_17 <- kl_V3846 `pseq` tl kl_V3846
                                                                                                                      appl_17 `pseq` kl_shen_trim_gubbins appl_17
                                                                                                Atom (B (False)) -> do !kl_if_18 <- let pat_cond_19 kl_V3846 kl_V3846h kl_V3846t = do !appl_20 <- kl_shen_tab
                                                                                                                                                                                      !kl_if_21 <- kl_V3846h `pseq` (appl_20 `pseq` eq kl_V3846h appl_20)
                                                                                                                                                                                      case kl_if_21 of
                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                        pat_cond_22 = do do return (Atom (B False))
                                                                                                                                     in case kl_V3846 of
                                                                                                                                            !(kl_V3846@(Cons (!kl_V3846h)
                                                                                                                                                             (!kl_V3846t))) -> pat_cond_19 kl_V3846 kl_V3846h kl_V3846t
                                                                                                                                            _ -> pat_cond_22
                                                                                                                       case kl_if_18 of
                                                                                                                           Atom (B (True)) -> do !appl_23 <- kl_V3846 `pseq` tl kl_V3846
                                                                                                                                                 appl_23 `pseq` kl_shen_trim_gubbins appl_23
                                                                                                                           Atom (B (False)) -> do !kl_if_24 <- let pat_cond_25 kl_V3846 kl_V3846h kl_V3846t = do !appl_26 <- kl_shen_left_round
                                                                                                                                                                                                                 !kl_if_27 <- kl_V3846h `pseq` (appl_26 `pseq` eq kl_V3846h appl_26)
                                                                                                                                                                                                                 case kl_if_27 of
                                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                   pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                in case kl_V3846 of
                                                                                                                                                                       !(kl_V3846@(Cons (!kl_V3846h)
                                                                                                                                                                                        (!kl_V3846t))) -> pat_cond_25 kl_V3846 kl_V3846h kl_V3846t
                                                                                                                                                                       _ -> pat_cond_28
                                                                                                                                                  case kl_if_24 of
                                                                                                                                                      Atom (B (True)) -> do !appl_29 <- kl_V3846 `pseq` tl kl_V3846
                                                                                                                                                                            appl_29 `pseq` kl_shen_trim_gubbins appl_29
                                                                                                                                                      Atom (B (False)) -> do do return kl_V3846
                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                _ -> throwError "if: expected boolean"
                                                                     _ -> throwError "if: expected boolean"
                                          _ -> throwError "if: expected boolean"

kl_shen_space :: Core.Types.KLContext Core.Types.Env
                                      Core.Types.KLValue
kl_shen_space = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 32)))

kl_shen_tab :: Core.Types.KLContext Core.Types.Env
                                    Core.Types.KLValue
kl_shen_tab = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 9)))

kl_shen_left_round :: Core.Types.KLContext Core.Types.Env
                                           Core.Types.KLValue
kl_shen_left_round = do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 40)))

kl_shen_find :: Core.Types.KLValue ->
                Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_find (!kl_V3855) (!kl_V3856) = do let !appl_0 = Atom Nil
                                          !kl_if_1 <- appl_0 `pseq` (kl_V3856 `pseq` eq appl_0 kl_V3856)
                                          case kl_if_1 of
                                              Atom (B (True)) -> do return (Atom Nil)
                                              Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V3856 kl_V3856h kl_V3856t = do !kl_if_4 <- kl_V3856h `pseq` applyWrapper kl_V3855 [kl_V3856h]
                                                                                                                                  case kl_if_4 of
                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                     pat_cond_5 = do do return (Atom (B False))
                                                                                  in case kl_V3856 of
                                                                                         !(kl_V3856@(Cons (!kl_V3856h)
                                                                                                          (!kl_V3856t))) -> pat_cond_3 kl_V3856 kl_V3856h kl_V3856t
                                                                                         _ -> pat_cond_5
                                                                     case kl_if_2 of
                                                                         Atom (B (True)) -> do !appl_6 <- kl_V3856 `pseq` hd kl_V3856
                                                                                               !appl_7 <- kl_V3856 `pseq` tl kl_V3856
                                                                                               !appl_8 <- kl_V3855 `pseq` (appl_7 `pseq` kl_shen_find kl_V3855 appl_7)
                                                                                               appl_6 `pseq` (appl_8 `pseq` klCons appl_6 appl_8)
                                                                         Atom (B (False)) -> do let pat_cond_9 kl_V3856 kl_V3856h kl_V3856t = do kl_V3855 `pseq` (kl_V3856t `pseq` kl_shen_find kl_V3855 kl_V3856t)
                                                                                                    pat_cond_10 = do do let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                        applyWrapper aw_11 [ApplC (wrapNamed "shen.find" kl_shen_find)]
                                                                                                 in case kl_V3856 of
                                                                                                        !(kl_V3856@(Cons (!kl_V3856h)
                                                                                                                         (!kl_V3856t))) -> pat_cond_9 kl_V3856 kl_V3856h kl_V3856t
                                                                                                        _ -> pat_cond_10
                                                                         _ -> throwError "if: expected boolean"
                                              _ -> throwError "if: expected boolean"

kl_shen_prefixP :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_prefixP (!kl_V3870) (!kl_V3871) = do let !appl_0 = Atom Nil
                                             !kl_if_1 <- appl_0 `pseq` (kl_V3870 `pseq` eq appl_0 kl_V3870)
                                             case kl_if_1 of
                                                 Atom (B (True)) -> do return (Atom (B True))
                                                 Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V3870 kl_V3870h kl_V3870t = do let pat_cond_4 kl_V3871 kl_V3871h kl_V3871t = do return (Atom (B True))
                                                                                                                                         pat_cond_5 = do do return (Atom (B False))
                                                                                                                                      in case kl_V3871 of
                                                                                                                                             !(kl_V3871@(Cons (!kl_V3871h)
                                                                                                                                                              (!kl_V3871t))) | eqCore kl_V3871h kl_V3870h -> pat_cond_4 kl_V3871 kl_V3871h kl_V3871t
                                                                                                                                             _ -> pat_cond_5
                                                                                        pat_cond_6 = do do return (Atom (B False))
                                                                                     in case kl_V3870 of
                                                                                            !(kl_V3870@(Cons (!kl_V3870h)
                                                                                                             (!kl_V3870t))) -> pat_cond_3 kl_V3870 kl_V3870h kl_V3870t
                                                                                            _ -> pat_cond_6
                                                                        case kl_if_2 of
                                                                            Atom (B (True)) -> do !appl_7 <- kl_V3870 `pseq` tl kl_V3870
                                                                                                  !appl_8 <- kl_V3871 `pseq` tl kl_V3871
                                                                                                  appl_7 `pseq` (appl_8 `pseq` kl_shen_prefixP appl_7 appl_8)
                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                            _ -> throwError "if: expected boolean"
                                                 _ -> throwError "if: expected boolean"

kl_shen_print_past_inputs :: Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_print_past_inputs (!kl_V3883) (!kl_V3884) (!kl_V3885) = do let !appl_0 = Atom Nil
                                                                   !kl_if_1 <- appl_0 `pseq` (kl_V3884 `pseq` eq appl_0 kl_V3884)
                                                                   case kl_if_1 of
                                                                       Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.UnboundSym "_"))
                                                                       Atom (B (False)) -> do !kl_if_2 <- let pat_cond_3 kl_V3884 kl_V3884h kl_V3884t = do !appl_4 <- kl_V3884h `pseq` applyWrapper kl_V3883 [kl_V3884h]
                                                                                                                                                           let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "not")
                                                                                                                                                           !kl_if_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4]
                                                                                                                                                           case kl_if_6 of
                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                              pat_cond_7 = do do return (Atom (B False))
                                                                                                           in case kl_V3884 of
                                                                                                                  !(kl_V3884@(Cons (!kl_V3884h)
                                                                                                                                   (!kl_V3884t))) -> pat_cond_3 kl_V3884 kl_V3884h kl_V3884t
                                                                                                                  _ -> pat_cond_7
                                                                                              case kl_if_2 of
                                                                                                  Atom (B (True)) -> do !appl_8 <- kl_V3884 `pseq` tl kl_V3884
                                                                                                                        !appl_9 <- kl_V3885 `pseq` add kl_V3885 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                        kl_V3883 `pseq` (appl_8 `pseq` (appl_9 `pseq` kl_shen_print_past_inputs kl_V3883 appl_8 appl_9))
                                                                                                  Atom (B (False)) -> do !kl_if_10 <- let pat_cond_11 kl_V3884 kl_V3884h kl_V3884t = do let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "tuple?")
                                                                                                                                                                                        !kl_if_13 <- kl_V3884h `pseq` applyWrapper aw_12 [kl_V3884h]
                                                                                                                                                                                        case kl_if_13 of
                                                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                          pat_cond_14 = do do return (Atom (B False))
                                                                                                                                       in case kl_V3884 of
                                                                                                                                              !(kl_V3884@(Cons (!kl_V3884h)
                                                                                                                                                               (!kl_V3884t))) -> pat_cond_11 kl_V3884 kl_V3884h kl_V3884t
                                                                                                                                              _ -> pat_cond_14
                                                                                                                         case kl_if_10 of
                                                                                                                             Atom (B (True)) -> do let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                   !appl_16 <- kl_V3885 `pseq` applyWrapper aw_15 [kl_V3885,
                                                                                                                                                                                                   Core.Types.Atom (Core.Types.Str ". "),
                                                                                                                                                                                                   Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                                                                                                   let !aw_17 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                                                                                                                                                   !appl_18 <- applyWrapper aw_17 []
                                                                                                                                                   let !aw_19 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                                                   !appl_20 <- appl_16 `pseq` (appl_18 `pseq` applyWrapper aw_19 [appl_16,
                                                                                                                                                                                                                  appl_18])
                                                                                                                                                   !appl_21 <- kl_V3884 `pseq` hd kl_V3884
                                                                                                                                                   let !aw_22 = Core.Types.Atom (Core.Types.UnboundSym "snd")
                                                                                                                                                   !appl_23 <- appl_21 `pseq` applyWrapper aw_22 [appl_21]
                                                                                                                                                   !appl_24 <- appl_23 `pseq` kl_shen_prbytes appl_23
                                                                                                                                                   !appl_25 <- kl_V3884 `pseq` tl kl_V3884
                                                                                                                                                   !appl_26 <- kl_V3885 `pseq` add kl_V3885 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                   !appl_27 <- kl_V3883 `pseq` (appl_25 `pseq` (appl_26 `pseq` kl_shen_print_past_inputs kl_V3883 appl_25 appl_26))
                                                                                                                                                   let !aw_28 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                                                                                                                                   !appl_29 <- appl_24 `pseq` (appl_27 `pseq` applyWrapper aw_28 [appl_24,
                                                                                                                                                                                                                  appl_27])
                                                                                                                                                   let !aw_30 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                                                                                                                                   appl_20 `pseq` (appl_29 `pseq` applyWrapper aw_30 [appl_20,
                                                                                                                                                                                                      appl_29])
                                                                                                                             Atom (B (False)) -> do do let !aw_31 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                                       applyWrapper aw_31 [ApplC (wrapNamed "shen.print-past-inputs" kl_shen_print_past_inputs)]
                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                  _ -> throwError "if: expected boolean"
                                                                       _ -> throwError "if: expected boolean"

kl_shen_toplevel_evaluate :: Core.Types.KLValue ->
                             Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_toplevel_evaluate (!kl_V3888) (!kl_V3889) = do !kl_if_0 <- let pat_cond_1 kl_V3888 kl_V3888h kl_V3888t = do !kl_if_2 <- let pat_cond_3 kl_V3888t kl_V3888th kl_V3888tt = do !kl_if_4 <- let pat_cond_5 = do !kl_if_6 <- let pat_cond_7 kl_V3888tt kl_V3888tth kl_V3888ttt = do let !appl_8 = Atom Nil
                                                                                                                                                                                                                                                                                       !kl_if_9 <- appl_8 `pseq` (kl_V3888ttt `pseq` eq appl_8 kl_V3888ttt)
                                                                                                                                                                                                                                                                                       !kl_if_10 <- case kl_if_9 of
                                                                                                                                                                                                                                                                                                        Atom (B (True)) -> do let pat_cond_11 = do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                  pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                               in case kl_V3889 of
                                                                                                                                                                                                                                                                                                                                      kl_V3889@(Atom (UnboundSym "true")) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                      kl_V3889@(Atom (B (True))) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                      _ -> pat_cond_12
                                                                                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                       case kl_if_10 of
                                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                    pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                                                 in case kl_V3888tt of
                                                                                                                                                                                                                                        !(kl_V3888tt@(Cons (!kl_V3888tth)
                                                                                                                                                                                                                                                           (!kl_V3888ttt))) -> pat_cond_7 kl_V3888tt kl_V3888tth kl_V3888ttt
                                                                                                                                                                                                                                        _ -> pat_cond_13
                                                                                                                                                                                                                    case kl_if_6 of
                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                    pat_cond_14 = do do return (Atom (B False))
                                                                                                                                                                                                 in case kl_V3888th of
                                                                                                                                                                                                        kl_V3888th@(Atom (UnboundSym ":")) -> pat_cond_5
                                                                                                                                                                                                        kl_V3888th@(ApplC (PL ":"
                                                                                                                                                                                                                              _)) -> pat_cond_5
                                                                                                                                                                                                        kl_V3888th@(ApplC (Func ":"
                                                                                                                                                                                                                                _)) -> pat_cond_5
                                                                                                                                                                                                        _ -> pat_cond_14
                                                                                                                                                                                    case kl_if_4 of
                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                    pat_cond_15 = do do return (Atom (B False))
                                                                                                                                 in case kl_V3888t of
                                                                                                                                        !(kl_V3888t@(Cons (!kl_V3888th)
                                                                                                                                                          (!kl_V3888tt))) -> pat_cond_3 kl_V3888t kl_V3888th kl_V3888tt
                                                                                                                                        _ -> pat_cond_15
                                                                                                                    case kl_if_2 of
                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                        _ -> throwError "if: expected boolean"
                                                                       pat_cond_16 = do do return (Atom (B False))
                                                                    in case kl_V3888 of
                                                                           !(kl_V3888@(Cons (!kl_V3888h)
                                                                                            (!kl_V3888t))) -> pat_cond_1 kl_V3888 kl_V3888h kl_V3888t
                                                                           _ -> pat_cond_16
                                                       case kl_if_0 of
                                                           Atom (B (True)) -> do !appl_17 <- kl_V3888 `pseq` hd kl_V3888
                                                                                 !appl_18 <- kl_V3888 `pseq` tl kl_V3888
                                                                                 !appl_19 <- appl_18 `pseq` tl appl_18
                                                                                 !appl_20 <- appl_19 `pseq` hd appl_19
                                                                                 appl_17 `pseq` (appl_20 `pseq` kl_shen_typecheck_and_evaluate appl_17 appl_20)
                                                           Atom (B (False)) -> do let pat_cond_21 kl_V3888 kl_V3888h kl_V3888t kl_V3888th kl_V3888tt = do let !appl_22 = Atom Nil
                                                                                                                                                          !appl_23 <- kl_V3888h `pseq` (appl_22 `pseq` klCons kl_V3888h appl_22)
                                                                                                                                                          !appl_24 <- appl_23 `pseq` (kl_V3889 `pseq` kl_shen_toplevel_evaluate appl_23 kl_V3889)
                                                                                                                                                          let !aw_25 = Core.Types.Atom (Core.Types.UnboundSym "nl")
                                                                                                                                                          !appl_26 <- applyWrapper aw_25 [Core.Types.Atom (Core.Types.N (Core.Types.KI 1))]
                                                                                                                                                          !appl_27 <- kl_V3888t `pseq` (kl_V3889 `pseq` kl_shen_toplevel_evaluate kl_V3888t kl_V3889)
                                                                                                                                                          let !aw_28 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                                                                                                                                          !appl_29 <- appl_26 `pseq` (appl_27 `pseq` applyWrapper aw_28 [appl_26,
                                                                                                                                                                                                                         appl_27])
                                                                                                                                                          let !aw_30 = Core.Types.Atom (Core.Types.UnboundSym "do")
                                                                                                                                                          appl_24 `pseq` (appl_29 `pseq` applyWrapper aw_30 [appl_24,
                                                                                                                                                                                                             appl_29])
                                                                                      pat_cond_31 = do !kl_if_32 <- let pat_cond_33 kl_V3888 kl_V3888h kl_V3888t = do let !appl_34 = Atom Nil
                                                                                                                                                                      !kl_if_35 <- appl_34 `pseq` (kl_V3888t `pseq` eq appl_34 kl_V3888t)
                                                                                                                                                                      !kl_if_36 <- case kl_if_35 of
                                                                                                                                                                                       Atom (B (True)) -> do let pat_cond_37 = do return (Atom (B True))
                                                                                                                                                                                                                 pat_cond_38 = do do return (Atom (B False))
                                                                                                                                                                                                              in case kl_V3889 of
                                                                                                                                                                                                                     kl_V3889@(Atom (UnboundSym "true")) -> pat_cond_37
                                                                                                                                                                                                                     kl_V3889@(Atom (B (True))) -> pat_cond_37
                                                                                                                                                                                                                     _ -> pat_cond_38
                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                      case kl_if_36 of
                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                        pat_cond_39 = do do return (Atom (B False))
                                                                                                                     in case kl_V3888 of
                                                                                                                            !(kl_V3888@(Cons (!kl_V3888h)
                                                                                                                                             (!kl_V3888t))) -> pat_cond_33 kl_V3888 kl_V3888h kl_V3888t
                                                                                                                            _ -> pat_cond_39
                                                                                                       case kl_if_32 of
                                                                                                           Atom (B (True)) -> do !appl_40 <- kl_V3888 `pseq` hd kl_V3888
                                                                                                                                 let !aw_41 = Core.Types.Atom (Core.Types.UnboundSym "gensym")
                                                                                                                                 !appl_42 <- applyWrapper aw_41 [Core.Types.Atom (Core.Types.UnboundSym "A")]
                                                                                                                                 appl_40 `pseq` (appl_42 `pseq` kl_shen_typecheck_and_evaluate appl_40 appl_42)
                                                                                                           Atom (B (False)) -> do !kl_if_43 <- let pat_cond_44 kl_V3888 kl_V3888h kl_V3888t = do let !appl_45 = Atom Nil
                                                                                                                                                                                                 !kl_if_46 <- appl_45 `pseq` (kl_V3888t `pseq` eq appl_45 kl_V3888t)
                                                                                                                                                                                                 !kl_if_47 <- case kl_if_46 of
                                                                                                                                                                                                                  Atom (B (True)) -> do let pat_cond_48 = do return (Atom (B True))
                                                                                                                                                                                                                                            pat_cond_49 = do do return (Atom (B False))
                                                                                                                                                                                                                                         in case kl_V3889 of
                                                                                                                                                                                                                                                kl_V3889@(Atom (UnboundSym "false")) -> pat_cond_48
                                                                                                                                                                                                                                                kl_V3889@(Atom (B (False))) -> pat_cond_48
                                                                                                                                                                                                                                                _ -> pat_cond_49
                                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                                                 case kl_if_47 of
                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                   pat_cond_50 = do do return (Atom (B False))
                                                                                                                                                in case kl_V3888 of
                                                                                                                                                       !(kl_V3888@(Cons (!kl_V3888h)
                                                                                                                                                                        (!kl_V3888t))) -> pat_cond_44 kl_V3888 kl_V3888h kl_V3888t
                                                                                                                                                       _ -> pat_cond_50
                                                                                                                                  case kl_if_43 of
                                                                                                                                      Atom (B (True)) -> do let !appl_51 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do let !aw_52 = Core.Types.Atom (Core.Types.UnboundSym "print")
                                                                                                                                                                                                                            kl_Eval `pseq` applyWrapper aw_52 [kl_Eval])))
                                                                                                                                                            !appl_53 <- kl_V3888 `pseq` hd kl_V3888
                                                                                                                                                            let !aw_54 = Core.Types.Atom (Core.Types.UnboundSym "shen.eval-without-macros")
                                                                                                                                                            !appl_55 <- appl_53 `pseq` applyWrapper aw_54 [appl_53]
                                                                                                                                                            appl_55 `pseq` applyWrapper appl_51 [appl_55]
                                                                                                                                      Atom (B (False)) -> do do let !aw_56 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                                                applyWrapper aw_56 [ApplC (wrapNamed "shen.toplevel_evaluate" kl_shen_toplevel_evaluate)]
                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                           _ -> throwError "if: expected boolean"
                                                                                   in case kl_V3888 of
                                                                                          !(kl_V3888@(Cons (!kl_V3888h)
                                                                                                           (!(kl_V3888t@(Cons (!kl_V3888th)
                                                                                                                              (!kl_V3888tt)))))) -> pat_cond_21 kl_V3888 kl_V3888h kl_V3888t kl_V3888th kl_V3888tt
                                                                                          _ -> pat_cond_31
                                                           _ -> throwError "if: expected boolean"

kl_shen_typecheck_and_evaluate :: Core.Types.KLValue ->
                                  Core.Types.KLValue ->
                                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_typecheck_and_evaluate (!kl_V3892) (!kl_V3893) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Typecheck) -> do let pat_cond_1 = do simpleError (Core.Types.Atom (Core.Types.Str "type error\n"))
                                                                                                                                    pat_cond_2 = do do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Type) -> do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                     !appl_6 <- kl_Type `pseq` applyWrapper aw_5 [kl_Type,
                                                                                                                                                                                                                                                                                                                                  Core.Types.Atom (Core.Types.Str ""),
                                                                                                                                                                                                                                                                                                                                  Core.Types.Atom (Core.Types.UnboundSym "shen.r")]
                                                                                                                                                                                                                                                                                     !appl_7 <- appl_6 `pseq` cn (Core.Types.Atom (Core.Types.Str " : ")) appl_6
                                                                                                                                                                                                                                                                                     let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                     !appl_9 <- kl_Eval `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_Eval,
                                                                                                                                                                                                                                                                                                                                                 appl_7,
                                                                                                                                                                                                                                                                                                                                                 Core.Types.Atom (Core.Types.UnboundSym "shen.s")])
                                                                                                                                                                                                                                                                                     let !aw_10 = Core.Types.Atom (Core.Types.UnboundSym "stoutput")
                                                                                                                                                                                                                                                                                     !appl_11 <- applyWrapper aw_10 []
                                                                                                                                                                                                                                                                                     let !aw_12 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                                     appl_9 `pseq` (appl_11 `pseq` applyWrapper aw_12 [appl_9,
                                                                                                                                                                                                                                                                                                                                       appl_11]))))
                                                                                                                                                                                                                      !appl_13 <- kl_Typecheck `pseq` kl_shen_pretty_type kl_Typecheck
                                                                                                                                                                                                                      appl_13 `pseq` applyWrapper appl_4 [appl_13])))
                                                                                                                                                       let !aw_14 = Core.Types.Atom (Core.Types.UnboundSym "shen.eval-without-macros")
                                                                                                                                                       !appl_15 <- kl_V3892 `pseq` applyWrapper aw_14 [kl_V3892]
                                                                                                                                                       appl_15 `pseq` applyWrapper appl_3 [appl_15]
                                                                                                                                 in case kl_Typecheck of
                                                                                                                                        kl_Typecheck@(Atom (UnboundSym "false")) -> pat_cond_1
                                                                                                                                        kl_Typecheck@(Atom (B (False))) -> pat_cond_1
                                                                                                                                        _ -> pat_cond_2)))
                                                            let !aw_16 = Core.Types.Atom (Core.Types.UnboundSym "shen.typecheck")
                                                            !appl_17 <- kl_V3892 `pseq` (kl_V3893 `pseq` applyWrapper aw_16 [kl_V3892,
                                                                                                                             kl_V3893])
                                                            appl_17 `pseq` applyWrapper appl_0 [appl_17]

kl_shen_pretty_type :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_pretty_type (!kl_V3895) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*alphabet*"))
                                     !appl_1 <- kl_V3895 `pseq` kl_shen_extract_pvars kl_V3895
                                     appl_0 `pseq` (appl_1 `pseq` (kl_V3895 `pseq` kl_shen_mult_subst appl_0 appl_1 kl_V3895))

kl_shen_extract_pvars :: Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_extract_pvars (!kl_V3901) = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "shen.pvar?")
                                       !kl_if_1 <- kl_V3901 `pseq` applyWrapper aw_0 [kl_V3901]
                                       case kl_if_1 of
                                           Atom (B (True)) -> do let !appl_2 = Atom Nil
                                                                 kl_V3901 `pseq` (appl_2 `pseq` klCons kl_V3901 appl_2)
                                           Atom (B (False)) -> do let pat_cond_3 kl_V3901 kl_V3901h kl_V3901t = do !appl_4 <- kl_V3901h `pseq` kl_shen_extract_pvars kl_V3901h
                                                                                                                   !appl_5 <- kl_V3901t `pseq` kl_shen_extract_pvars kl_V3901t
                                                                                                                   let !aw_6 = Core.Types.Atom (Core.Types.UnboundSym "union")
                                                                                                                   appl_4 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_4,
                                                                                                                                                                   appl_5])
                                                                      pat_cond_7 = do do return (Atom Nil)
                                                                   in case kl_V3901 of
                                                                          !(kl_V3901@(Cons (!kl_V3901h)
                                                                                           (!kl_V3901t))) -> pat_cond_3 kl_V3901 kl_V3901h kl_V3901t
                                                                          _ -> pat_cond_7
                                           _ -> throwError "if: expected boolean"

kl_shen_mult_subst :: Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_mult_subst (!kl_V3909) (!kl_V3910) (!kl_V3911) = do let !appl_0 = Atom Nil
                                                            !kl_if_1 <- appl_0 `pseq` (kl_V3909 `pseq` eq appl_0 kl_V3909)
                                                            case kl_if_1 of
                                                                Atom (B (True)) -> do return kl_V3911
                                                                Atom (B (False)) -> do let !appl_2 = Atom Nil
                                                                                       !kl_if_3 <- appl_2 `pseq` (kl_V3910 `pseq` eq appl_2 kl_V3910)
                                                                                       case kl_if_3 of
                                                                                           Atom (B (True)) -> do return kl_V3911
                                                                                           Atom (B (False)) -> do !kl_if_4 <- let pat_cond_5 kl_V3909 kl_V3909h kl_V3909t = do let pat_cond_6 kl_V3910 kl_V3910h kl_V3910t = do return (Atom (B True))
                                                                                                                                                                                   pat_cond_7 = do do return (Atom (B False))
                                                                                                                                                                                in case kl_V3910 of
                                                                                                                                                                                       !(kl_V3910@(Cons (!kl_V3910h)
                                                                                                                                                                                                        (!kl_V3910t))) -> pat_cond_6 kl_V3910 kl_V3910h kl_V3910t
                                                                                                                                                                                       _ -> pat_cond_7
                                                                                                                                  pat_cond_8 = do do return (Atom (B False))
                                                                                                                               in case kl_V3909 of
                                                                                                                                      !(kl_V3909@(Cons (!kl_V3909h)
                                                                                                                                                       (!kl_V3909t))) -> pat_cond_5 kl_V3909 kl_V3909h kl_V3909t
                                                                                                                                      _ -> pat_cond_8
                                                                                                                  case kl_if_4 of
                                                                                                                      Atom (B (True)) -> do !appl_9 <- kl_V3909 `pseq` tl kl_V3909
                                                                                                                                            !appl_10 <- kl_V3910 `pseq` tl kl_V3910
                                                                                                                                            !appl_11 <- kl_V3909 `pseq` hd kl_V3909
                                                                                                                                            !appl_12 <- kl_V3910 `pseq` hd kl_V3910
                                                                                                                                            let !aw_13 = Core.Types.Atom (Core.Types.UnboundSym "subst")
                                                                                                                                            !appl_14 <- appl_11 `pseq` (appl_12 `pseq` (kl_V3911 `pseq` applyWrapper aw_13 [appl_11,
                                                                                                                                                                                                                            appl_12,
                                                                                                                                                                                                                            kl_V3911]))
                                                                                                                                            appl_9 `pseq` (appl_10 `pseq` (appl_14 `pseq` kl_shen_mult_subst appl_9 appl_10 appl_14))
                                                                                                                      Atom (B (False)) -> do do let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "shen.f_error")
                                                                                                                                                applyWrapper aw_15 [ApplC (wrapNamed "shen.mult_subst" kl_shen_mult_subst)]
                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                           _ -> throwError "if: expected boolean"
                                                                _ -> throwError "if: expected boolean"

expr0 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr0 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
           (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*continue-repl-loop*")) (Atom (B True))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
           (do let !appl_0 = Atom Nil
               appl_0 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*history*")) appl_0) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
