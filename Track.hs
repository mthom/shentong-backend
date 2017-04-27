{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Track where

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

kl_shen_f_error :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_f_error (!kl_V3913) = do let !aw_0 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                 !appl_1 <- kl_V3913 `pseq` applyWrapper aw_0 [kl_V3913,
                                                                               Core.Types.Atom (Core.Types.Str ";\n"),
                                                                               Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                 !appl_2 <- appl_1 `pseq` cn (Core.Types.Atom (Core.Types.Str "partial function ")) appl_1
                                 !appl_3 <- kl_stoutput
                                 let !aw_4 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                 !appl_5 <- appl_2 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_2,
                                                                                            appl_3])
                                 !appl_6 <- kl_V3913 `pseq` kl_shen_trackedP kl_V3913
                                 !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                 !kl_if_8 <- case kl_if_7 of
                                                 Atom (B (True)) -> do let !aw_9 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                                       !appl_10 <- kl_V3913 `pseq` applyWrapper aw_9 [kl_V3913,
                                                                                                                      Core.Types.Atom (Core.Types.Str "? "),
                                                                                                                      Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                                       !appl_11 <- appl_10 `pseq` cn (Core.Types.Atom (Core.Types.Str "track ")) appl_10
                                                                       !kl_if_12 <- appl_11 `pseq` kl_y_or_nP appl_11
                                                                       case kl_if_12 of
                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                           _ -> throwError "if: expected boolean"
                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                 _ -> throwError "if: expected boolean"
                                 !appl_13 <- case kl_if_8 of
                                                 Atom (B (True)) -> do !appl_14 <- kl_V3913 `pseq` kl_ps kl_V3913
                                                                       appl_14 `pseq` kl_shen_track_function appl_14
                                                 Atom (B (False)) -> do do return (Core.Types.Atom (Core.Types.UnboundSym "shen.ok"))
                                                 _ -> throwError "if: expected boolean"
                                 !appl_15 <- simpleError (Core.Types.Atom (Core.Types.Str "aborted"))
                                 !appl_16 <- appl_13 `pseq` (appl_15 `pseq` kl_do appl_13 appl_15)
                                 appl_5 `pseq` (appl_16 `pseq` kl_do appl_5 appl_16)

kl_shen_trackedP :: Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_trackedP (!kl_V3915) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tracking*"))
                                  kl_V3915 `pseq` (appl_0 `pseq` kl_elementP kl_V3915 appl_0)

kl_track :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_track (!kl_V3917) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Source) -> do kl_Source `pseq` kl_shen_track_function kl_Source)))
                          !appl_1 <- kl_V3917 `pseq` kl_ps kl_V3917
                          appl_1 `pseq` applyWrapper appl_0 [appl_1]

kl_shen_track_function :: Core.Types.KLValue ->
                          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_track_function (!kl_V3919) = do !kl_if_0 <- let pat_cond_1 kl_V3919 kl_V3919h kl_V3919t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V3919t kl_V3919th kl_V3919tt = do !kl_if_6 <- let pat_cond_7 kl_V3919tt kl_V3919tth kl_V3919ttt = do !kl_if_8 <- let pat_cond_9 kl_V3919ttt kl_V3919ttth kl_V3919tttt = do let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                                                                                              !kl_if_11 <- appl_10 `pseq` (kl_V3919tttt `pseq` eq appl_10 kl_V3919tttt)
                                                                                                                                                                                                                                                                                                                                              case kl_if_11 of
                                                                                                                                                                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                        pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                     in case kl_V3919ttt of
                                                                                                                                                                                                                                                                                            !(kl_V3919ttt@(Cons (!kl_V3919ttth)
                                                                                                                                                                                                                                                                                                                (!kl_V3919tttt))) -> pat_cond_9 kl_V3919ttt kl_V3919ttth kl_V3919tttt
                                                                                                                                                                                                                                                                                            _ -> pat_cond_12
                                                                                                                                                                                                                                                                        case kl_if_8 of
                                                                                                                                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                     pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                                  in case kl_V3919tt of
                                                                                                                                                                                                                         !(kl_V3919tt@(Cons (!kl_V3919tth)
                                                                                                                                                                                                                                            (!kl_V3919ttt))) -> pat_cond_7 kl_V3919tt kl_V3919tth kl_V3919ttt
                                                                                                                                                                                                                         _ -> pat_cond_13
                                                                                                                                                                                                     case kl_if_6 of
                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                     pat_cond_14 = do do return (Atom (B False))
                                                                                                                                                  in case kl_V3919t of
                                                                                                                                                         !(kl_V3919t@(Cons (!kl_V3919th)
                                                                                                                                                                           (!kl_V3919tt))) -> pat_cond_5 kl_V3919t kl_V3919th kl_V3919tt
                                                                                                                                                         _ -> pat_cond_14
                                                                                                                                     case kl_if_4 of
                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                     pat_cond_15 = do do return (Atom (B False))
                                                                                                                  in case kl_V3919h of
                                                                                                                         kl_V3919h@(Atom (UnboundSym "defun")) -> pat_cond_3
                                                                                                                         kl_V3919h@(ApplC (PL "defun"
                                                                                                                                              _)) -> pat_cond_3
                                                                                                                         kl_V3919h@(ApplC (Func "defun"
                                                                                                                                                _)) -> pat_cond_3
                                                                                                                         _ -> pat_cond_15
                                                                                                     case kl_if_2 of
                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                         _ -> throwError "if: expected boolean"
                                                        pat_cond_16 = do do return (Atom (B False))
                                                     in case kl_V3919 of
                                                            !(kl_V3919@(Cons (!kl_V3919h)
                                                                             (!kl_V3919t))) -> pat_cond_1 kl_V3919 kl_V3919h kl_V3919t
                                                            _ -> pat_cond_16
                                        case kl_if_0 of
                                            Atom (B (True)) -> do let !appl_17 = ApplC (Func "lambda" (Context (\(!kl_KL) -> do let !appl_18 = ApplC (Func "lambda" (Context (\(!kl_Ob) -> do let !appl_19 = ApplC (Func "lambda" (Context (\(!kl_Tr) -> do return kl_Ob)))
                                                                                                                                                                                              !appl_20 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tracking*"))
                                                                                                                                                                                              !appl_21 <- kl_Ob `pseq` (appl_20 `pseq` klCons kl_Ob appl_20)
                                                                                                                                                                                              !appl_22 <- appl_21 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*tracking*")) appl_21
                                                                                                                                                                                              appl_22 `pseq` applyWrapper appl_19 [appl_22])))
                                                                                                                                !appl_23 <- kl_KL `pseq` evalKL kl_KL
                                                                                                                                appl_23 `pseq` applyWrapper appl_18 [appl_23])))
                                                                  !appl_24 <- kl_V3919 `pseq` tl kl_V3919
                                                                  !appl_25 <- appl_24 `pseq` hd appl_24
                                                                  !appl_26 <- kl_V3919 `pseq` tl kl_V3919
                                                                  !appl_27 <- appl_26 `pseq` tl appl_26
                                                                  !appl_28 <- appl_27 `pseq` hd appl_27
                                                                  !appl_29 <- kl_V3919 `pseq` tl kl_V3919
                                                                  !appl_30 <- appl_29 `pseq` hd appl_29
                                                                  !appl_31 <- kl_V3919 `pseq` tl kl_V3919
                                                                  !appl_32 <- appl_31 `pseq` tl appl_31
                                                                  !appl_33 <- appl_32 `pseq` hd appl_32
                                                                  !appl_34 <- kl_V3919 `pseq` tl kl_V3919
                                                                  !appl_35 <- appl_34 `pseq` tl appl_34
                                                                  !appl_36 <- appl_35 `pseq` tl appl_35
                                                                  !appl_37 <- appl_36 `pseq` hd appl_36
                                                                  !appl_38 <- appl_30 `pseq` (appl_33 `pseq` (appl_37 `pseq` kl_shen_insert_tracking_code appl_30 appl_33 appl_37))
                                                                  let !appl_39 = Atom Nil
                                                                  !appl_40 <- appl_38 `pseq` (appl_39 `pseq` klCons appl_38 appl_39)
                                                                  !appl_41 <- appl_28 `pseq` (appl_40 `pseq` klCons appl_28 appl_40)
                                                                  !appl_42 <- appl_25 `pseq` (appl_41 `pseq` klCons appl_25 appl_41)
                                                                  !appl_43 <- appl_42 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defun")) appl_42
                                                                  appl_43 `pseq` applyWrapper appl_17 [appl_43]
                                            Atom (B (False)) -> do do kl_shen_f_error (ApplC (wrapNamed "shen.track-function" kl_shen_track_function))
                                            _ -> throwError "if: expected boolean"

kl_shen_insert_tracking_code :: Core.Types.KLValue ->
                                Core.Types.KLValue ->
                                Core.Types.KLValue ->
                                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_insert_tracking_code (!kl_V3923) (!kl_V3924) (!kl_V3925) = do let !appl_0 = Atom Nil
                                                                      !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_0
                                                                      !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_1
                                                                      let !appl_3 = Atom Nil
                                                                      !appl_4 <- appl_3 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_3
                                                                      !appl_5 <- appl_2 `pseq` (appl_4 `pseq` klCons appl_2 appl_4)
                                                                      !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_5
                                                                      let !appl_7 = Atom Nil
                                                                      !appl_8 <- appl_6 `pseq` (appl_7 `pseq` klCons appl_6 appl_7)
                                                                      !appl_9 <- appl_8 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_8
                                                                      !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_9
                                                                      let !appl_11 = Atom Nil
                                                                      !appl_12 <- appl_11 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_11
                                                                      !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_12
                                                                      !appl_14 <- kl_V3924 `pseq` kl_shen_cons_form kl_V3924
                                                                      let !appl_15 = Atom Nil
                                                                      !appl_16 <- appl_14 `pseq` (appl_15 `pseq` klCons appl_14 appl_15)
                                                                      !appl_17 <- kl_V3923 `pseq` (appl_16 `pseq` klCons kl_V3923 appl_16)
                                                                      !appl_18 <- appl_13 `pseq` (appl_17 `pseq` klCons appl_13 appl_17)
                                                                      !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.input-track" kl_shen_input_track)) appl_18
                                                                      let !appl_20 = Atom Nil
                                                                      !appl_21 <- appl_20 `pseq` klCons (ApplC (PL "shen.terpri-or-read-char" kl_shen_terpri_or_read_char)) appl_20
                                                                      let !appl_22 = Atom Nil
                                                                      !appl_23 <- appl_22 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_22
                                                                      !appl_24 <- appl_23 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_23
                                                                      let !appl_25 = Atom Nil
                                                                      !appl_26 <- appl_25 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_25
                                                                      !appl_27 <- kl_V3923 `pseq` (appl_26 `pseq` klCons kl_V3923 appl_26)
                                                                      !appl_28 <- appl_24 `pseq` (appl_27 `pseq` klCons appl_24 appl_27)
                                                                      !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "shen.output-track" kl_shen_output_track)) appl_28
                                                                      let !appl_30 = Atom Nil
                                                                      !appl_31 <- appl_30 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_30
                                                                      !appl_32 <- appl_31 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_31
                                                                      let !appl_33 = Atom Nil
                                                                      !appl_34 <- appl_33 `pseq` klCons (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) appl_33
                                                                      !appl_35 <- appl_32 `pseq` (appl_34 `pseq` klCons appl_32 appl_34)
                                                                      !appl_36 <- appl_35 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_35
                                                                      let !appl_37 = Atom Nil
                                                                      !appl_38 <- appl_36 `pseq` (appl_37 `pseq` klCons appl_36 appl_37)
                                                                      !appl_39 <- appl_38 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.*call*")) appl_38
                                                                      !appl_40 <- appl_39 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_39
                                                                      let !appl_41 = Atom Nil
                                                                      !appl_42 <- appl_41 `pseq` klCons (ApplC (PL "shen.terpri-or-read-char" kl_shen_terpri_or_read_char)) appl_41
                                                                      let !appl_43 = Atom Nil
                                                                      !appl_44 <- appl_43 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_43
                                                                      !appl_45 <- appl_42 `pseq` (appl_44 `pseq` klCons appl_42 appl_44)
                                                                      !appl_46 <- appl_45 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_45
                                                                      let !appl_47 = Atom Nil
                                                                      !appl_48 <- appl_46 `pseq` (appl_47 `pseq` klCons appl_46 appl_47)
                                                                      !appl_49 <- appl_40 `pseq` (appl_48 `pseq` klCons appl_40 appl_48)
                                                                      !appl_50 <- appl_49 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_49
                                                                      let !appl_51 = Atom Nil
                                                                      !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                                                                      !appl_53 <- appl_29 `pseq` (appl_52 `pseq` klCons appl_29 appl_52)
                                                                      !appl_54 <- appl_53 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_53
                                                                      let !appl_55 = Atom Nil
                                                                      !appl_56 <- appl_54 `pseq` (appl_55 `pseq` klCons appl_54 appl_55)
                                                                      !appl_57 <- kl_V3925 `pseq` (appl_56 `pseq` klCons kl_V3925 appl_56)
                                                                      !appl_58 <- appl_57 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_57
                                                                      !appl_59 <- appl_58 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_58
                                                                      let !appl_60 = Atom Nil
                                                                      !appl_61 <- appl_59 `pseq` (appl_60 `pseq` klCons appl_59 appl_60)
                                                                      !appl_62 <- appl_21 `pseq` (appl_61 `pseq` klCons appl_21 appl_61)
                                                                      !appl_63 <- appl_62 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_62
                                                                      let !appl_64 = Atom Nil
                                                                      !appl_65 <- appl_63 `pseq` (appl_64 `pseq` klCons appl_63 appl_64)
                                                                      !appl_66 <- appl_19 `pseq` (appl_65 `pseq` klCons appl_19 appl_65)
                                                                      !appl_67 <- appl_66 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_66
                                                                      let !appl_68 = Atom Nil
                                                                      !appl_69 <- appl_67 `pseq` (appl_68 `pseq` klCons appl_67 appl_68)
                                                                      !appl_70 <- appl_10 `pseq` (appl_69 `pseq` klCons appl_10 appl_69)
                                                                      appl_70 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_70

kl_step :: Core.Types.KLValue ->
           Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_step (!kl_V3931) = do let pat_cond_0 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*step*")) (Atom (B True))
                             pat_cond_1 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*step*")) (Atom (B False))
                             pat_cond_2 = do do simpleError (Core.Types.Atom (Core.Types.Str "step expects a + or a -.\n"))
                          in case kl_V3931 of
                                 kl_V3931@(Atom (UnboundSym "+")) -> pat_cond_0
                                 kl_V3931@(ApplC (PL "+" _)) -> pat_cond_0
                                 kl_V3931@(ApplC (Func "+" _)) -> pat_cond_0
                                 kl_V3931@(Atom (UnboundSym "-")) -> pat_cond_1
                                 kl_V3931@(ApplC (PL "-" _)) -> pat_cond_1
                                 kl_V3931@(ApplC (Func "-" _)) -> pat_cond_1
                                 _ -> pat_cond_2

kl_spy :: Core.Types.KLValue ->
          Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_spy (!kl_V3937) = do let pat_cond_0 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*spy*")) (Atom (B True))
                            pat_cond_1 = do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*spy*")) (Atom (B False))
                            pat_cond_2 = do do simpleError (Core.Types.Atom (Core.Types.Str "spy expects a + or a -.\n"))
                         in case kl_V3937 of
                                kl_V3937@(Atom (UnboundSym "+")) -> pat_cond_0
                                kl_V3937@(ApplC (PL "+" _)) -> pat_cond_0
                                kl_V3937@(ApplC (Func "+" _)) -> pat_cond_0
                                kl_V3937@(Atom (UnboundSym "-")) -> pat_cond_1
                                kl_V3937@(ApplC (PL "-" _)) -> pat_cond_1
                                kl_V3937@(ApplC (Func "-" _)) -> pat_cond_1
                                _ -> pat_cond_2

kl_shen_terpri_or_read_char :: Core.Types.KLContext Core.Types.Env
                                                    Core.Types.KLValue
kl_shen_terpri_or_read_char = do !kl_if_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*step*"))
                                 case kl_if_0 of
                                     Atom (B (True)) -> do !appl_1 <- value (Core.Types.Atom (Core.Types.UnboundSym "*stinput*"))
                                                           !appl_2 <- appl_1 `pseq` readByte appl_1
                                                           appl_2 `pseq` kl_shen_check_byte appl_2
                                     Atom (B (False)) -> do do kl_nl (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                     _ -> throwError "if: expected boolean"

kl_shen_check_byte :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_check_byte (!kl_V3943) = do !appl_0 <- kl_shen_hat
                                    !kl_if_1 <- kl_V3943 `pseq` (appl_0 `pseq` eq kl_V3943 appl_0)
                                    case kl_if_1 of
                                        Atom (B (True)) -> do simpleError (Core.Types.Atom (Core.Types.Str "aborted"))
                                        Atom (B (False)) -> do do return (Atom (B True))
                                        _ -> throwError "if: expected boolean"

kl_shen_input_track :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_input_track (!kl_V3947) (!kl_V3948) (!kl_V3949) = do !appl_0 <- kl_V3947 `pseq` kl_shen_spaces kl_V3947
                                                             !appl_1 <- kl_V3947 `pseq` kl_shen_spaces kl_V3947
                                                             let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                             !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [appl_1,
                                                                                                         Core.Types.Atom (Core.Types.Str ""),
                                                                                                         Core.Types.Atom (Core.Types.UnboundSym "shen.a")]
                                                             !appl_4 <- appl_3 `pseq` cn (Core.Types.Atom (Core.Types.Str " \n")) appl_3
                                                             let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                             !appl_6 <- kl_V3948 `pseq` (appl_4 `pseq` applyWrapper aw_5 [kl_V3948,
                                                                                                                          appl_4,
                                                                                                                          Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                             !appl_7 <- appl_6 `pseq` cn (Core.Types.Atom (Core.Types.Str "> Inputs to ")) appl_6
                                                             let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                             !appl_9 <- kl_V3947 `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_V3947,
                                                                                                                          appl_7,
                                                                                                                          Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                             !appl_10 <- appl_9 `pseq` cn (Core.Types.Atom (Core.Types.Str "<")) appl_9
                                                             let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                             !appl_12 <- appl_0 `pseq` (appl_10 `pseq` applyWrapper aw_11 [appl_0,
                                                                                                                           appl_10,
                                                                                                                           Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                             !appl_13 <- appl_12 `pseq` cn (Core.Types.Atom (Core.Types.Str "\n")) appl_12
                                                             !appl_14 <- kl_stoutput
                                                             let !aw_15 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                             !appl_16 <- appl_13 `pseq` (appl_14 `pseq` applyWrapper aw_15 [appl_13,
                                                                                                                            appl_14])
                                                             !appl_17 <- kl_V3949 `pseq` kl_shen_recursively_print kl_V3949
                                                             appl_16 `pseq` (appl_17 `pseq` kl_do appl_16 appl_17)

kl_shen_recursively_print :: Core.Types.KLValue ->
                             Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_recursively_print (!kl_V3951) = do let !appl_0 = Atom Nil
                                           !kl_if_1 <- appl_0 `pseq` (kl_V3951 `pseq` eq appl_0 kl_V3951)
                                           case kl_if_1 of
                                               Atom (B (True)) -> do !appl_2 <- kl_stoutput
                                                                     let !aw_3 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                     appl_2 `pseq` applyWrapper aw_3 [Core.Types.Atom (Core.Types.Str " ==>"),
                                                                                                      appl_2]
                                               Atom (B (False)) -> do let pat_cond_4 kl_V3951 kl_V3951h kl_V3951t = do let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "print")
                                                                                                                       !appl_6 <- kl_V3951h `pseq` applyWrapper aw_5 [kl_V3951h]
                                                                                                                       !appl_7 <- kl_stoutput
                                                                                                                       let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                                                                                       !appl_9 <- appl_7 `pseq` applyWrapper aw_8 [Core.Types.Atom (Core.Types.Str ", "),
                                                                                                                                                                   appl_7]
                                                                                                                       !appl_10 <- kl_V3951t `pseq` kl_shen_recursively_print kl_V3951t
                                                                                                                       !appl_11 <- appl_9 `pseq` (appl_10 `pseq` kl_do appl_9 appl_10)
                                                                                                                       appl_6 `pseq` (appl_11 `pseq` kl_do appl_6 appl_11)
                                                                          pat_cond_12 = do do kl_shen_f_error (ApplC (wrapNamed "shen.recursively-print" kl_shen_recursively_print))
                                                                       in case kl_V3951 of
                                                                              !(kl_V3951@(Cons (!kl_V3951h)
                                                                                               (!kl_V3951t))) -> pat_cond_4 kl_V3951 kl_V3951h kl_V3951t
                                                                              _ -> pat_cond_12
                                               _ -> throwError "if: expected boolean"

kl_shen_spaces :: Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_spaces (!kl_V3953) = do let pat_cond_0 = do return (Core.Types.Atom (Core.Types.Str ""))
                                    pat_cond_1 = do do !appl_2 <- kl_V3953 `pseq` Primitives.subtract kl_V3953 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                       !appl_3 <- appl_2 `pseq` kl_shen_spaces appl_2
                                                       appl_3 `pseq` cn (Core.Types.Atom (Core.Types.Str " ")) appl_3
                                 in case kl_V3953 of
                                        kl_V3953@(Atom (N (KI 0))) -> pat_cond_0
                                        _ -> pat_cond_1

kl_shen_output_track :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_output_track (!kl_V3957) (!kl_V3958) (!kl_V3959) = do !appl_0 <- kl_V3957 `pseq` kl_shen_spaces kl_V3957
                                                              !appl_1 <- kl_V3957 `pseq` kl_shen_spaces kl_V3957
                                                              let !aw_2 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                              !appl_3 <- kl_V3959 `pseq` applyWrapper aw_2 [kl_V3959,
                                                                                                            Core.Types.Atom (Core.Types.Str ""),
                                                                                                            Core.Types.Atom (Core.Types.UnboundSym "shen.s")]
                                                              !appl_4 <- appl_3 `pseq` cn (Core.Types.Atom (Core.Types.Str "==> ")) appl_3
                                                              let !aw_5 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                              !appl_6 <- appl_1 `pseq` (appl_4 `pseq` applyWrapper aw_5 [appl_1,
                                                                                                                         appl_4,
                                                                                                                         Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                              !appl_7 <- appl_6 `pseq` cn (Core.Types.Atom (Core.Types.Str " \n")) appl_6
                                                              let !aw_8 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                              !appl_9 <- kl_V3958 `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_V3958,
                                                                                                                           appl_7,
                                                                                                                           Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                              !appl_10 <- appl_9 `pseq` cn (Core.Types.Atom (Core.Types.Str "> Output from ")) appl_9
                                                              let !aw_11 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                              !appl_12 <- kl_V3957 `pseq` (appl_10 `pseq` applyWrapper aw_11 [kl_V3957,
                                                                                                                              appl_10,
                                                                                                                              Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                              !appl_13 <- appl_12 `pseq` cn (Core.Types.Atom (Core.Types.Str "<")) appl_12
                                                              let !aw_14 = Core.Types.Atom (Core.Types.UnboundSym "shen.app")
                                                              !appl_15 <- appl_0 `pseq` (appl_13 `pseq` applyWrapper aw_14 [appl_0,
                                                                                                                            appl_13,
                                                                                                                            Core.Types.Atom (Core.Types.UnboundSym "shen.a")])
                                                              !appl_16 <- appl_15 `pseq` cn (Core.Types.Atom (Core.Types.Str "\n")) appl_15
                                                              !appl_17 <- kl_stoutput
                                                              let !aw_18 = Core.Types.Atom (Core.Types.UnboundSym "shen.prhush")
                                                              appl_16 `pseq` (appl_17 `pseq` applyWrapper aw_18 [appl_16,
                                                                                                                 appl_17])

kl_untrack :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_untrack (!kl_V3961) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Tracking) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Tracking) -> do !appl_2 <- kl_V3961 `pseq` kl_ps kl_V3961
                                                                                                                                                                  appl_2 `pseq` kl_eval appl_2)))
                                                                                               !appl_3 <- kl_V3961 `pseq` (kl_Tracking `pseq` kl_remove kl_V3961 kl_Tracking)
                                                                                               !appl_4 <- appl_3 `pseq` klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*tracking*")) appl_3
                                                                                               appl_4 `pseq` applyWrapper appl_1 [appl_4])))
                            !appl_5 <- value (Core.Types.Atom (Core.Types.UnboundSym "shen.*tracking*"))
                            appl_5 `pseq` applyWrapper appl_0 [appl_5]

kl_profile :: Core.Types.KLValue ->
              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_profile (!kl_V3963) = do !appl_0 <- kl_V3963 `pseq` kl_ps kl_V3963
                            appl_0 `pseq` kl_shen_profile_help appl_0

kl_shen_profile_help :: Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_profile_help (!kl_V3969) = do !kl_if_0 <- let pat_cond_1 kl_V3969 kl_V3969h kl_V3969t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V3969t kl_V3969th kl_V3969tt = do !kl_if_6 <- let pat_cond_7 kl_V3969tt kl_V3969tth kl_V3969ttt = do !kl_if_8 <- let pat_cond_9 kl_V3969ttt kl_V3969ttth kl_V3969tttt = do let !appl_10 = Atom Nil
                                                                                                                                                                                                                                                                                                                                            !kl_if_11 <- appl_10 `pseq` (kl_V3969tttt `pseq` eq appl_10 kl_V3969tttt)
                                                                                                                                                                                                                                                                                                                                            case kl_if_11 of
                                                                                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                      pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                   in case kl_V3969ttt of
                                                                                                                                                                                                                                                                                          !(kl_V3969ttt@(Cons (!kl_V3969ttth)
                                                                                                                                                                                                                                                                                                              (!kl_V3969tttt))) -> pat_cond_9 kl_V3969ttt kl_V3969ttth kl_V3969tttt
                                                                                                                                                                                                                                                                                          _ -> pat_cond_12
                                                                                                                                                                                                                                                                      case kl_if_8 of
                                                                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                   pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                                in case kl_V3969tt of
                                                                                                                                                                                                                       !(kl_V3969tt@(Cons (!kl_V3969tth)
                                                                                                                                                                                                                                          (!kl_V3969ttt))) -> pat_cond_7 kl_V3969tt kl_V3969tth kl_V3969ttt
                                                                                                                                                                                                                       _ -> pat_cond_13
                                                                                                                                                                                                   case kl_if_6 of
                                                                                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                   pat_cond_14 = do do return (Atom (B False))
                                                                                                                                                in case kl_V3969t of
                                                                                                                                                       !(kl_V3969t@(Cons (!kl_V3969th)
                                                                                                                                                                         (!kl_V3969tt))) -> pat_cond_5 kl_V3969t kl_V3969th kl_V3969tt
                                                                                                                                                       _ -> pat_cond_14
                                                                                                                                   case kl_if_4 of
                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                   pat_cond_15 = do do return (Atom (B False))
                                                                                                                in case kl_V3969h of
                                                                                                                       kl_V3969h@(Atom (UnboundSym "defun")) -> pat_cond_3
                                                                                                                       kl_V3969h@(ApplC (PL "defun"
                                                                                                                                            _)) -> pat_cond_3
                                                                                                                       kl_V3969h@(ApplC (Func "defun"
                                                                                                                                              _)) -> pat_cond_3
                                                                                                                       _ -> pat_cond_15
                                                                                                   case kl_if_2 of
                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                       _ -> throwError "if: expected boolean"
                                                      pat_cond_16 = do do return (Atom (B False))
                                                   in case kl_V3969 of
                                                          !(kl_V3969@(Cons (!kl_V3969h)
                                                                           (!kl_V3969t))) -> pat_cond_1 kl_V3969 kl_V3969h kl_V3969t
                                                          _ -> pat_cond_16
                                      case kl_if_0 of
                                          Atom (B (True)) -> do let !appl_17 = ApplC (Func "lambda" (Context (\(!kl_G) -> do let !appl_18 = ApplC (Func "lambda" (Context (\(!kl_Profile) -> do let !appl_19 = ApplC (Func "lambda" (Context (\(!kl_Def) -> do let !appl_20 = ApplC (Func "lambda" (Context (\(!kl_CompileProfile) -> do let !appl_21 = ApplC (Func "lambda" (Context (\(!kl_CompileG) -> do !appl_22 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                                                                                                                                                                                                                                                                                                             appl_22 `pseq` hd appl_22)))
                                                                                                                                                                                                                                                                                                                                         !appl_23 <- kl_Def `pseq` kl_shen_eval_without_macros kl_Def
                                                                                                                                                                                                                                                                                                                                         appl_23 `pseq` applyWrapper appl_21 [appl_23])))
                                                                                                                                                                                                                                                               !appl_24 <- kl_Profile `pseq` kl_shen_eval_without_macros kl_Profile
                                                                                                                                                                                                                                                               appl_24 `pseq` applyWrapper appl_20 [appl_24])))
                                                                                                                                                                                                !appl_25 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                                                                                                !appl_26 <- appl_25 `pseq` tl appl_25
                                                                                                                                                                                                !appl_27 <- appl_26 `pseq` hd appl_26
                                                                                                                                                                                                !appl_28 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                                                                                                !appl_29 <- appl_28 `pseq` hd appl_28
                                                                                                                                                                                                !appl_30 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                                                                                                !appl_31 <- appl_30 `pseq` tl appl_30
                                                                                                                                                                                                !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                                !appl_33 <- appl_32 `pseq` hd appl_32
                                                                                                                                                                                                !appl_34 <- kl_G `pseq` (appl_29 `pseq` (appl_33 `pseq` kl_subst kl_G appl_29 appl_33))
                                                                                                                                                                                                let !appl_35 = Atom Nil
                                                                                                                                                                                                !appl_36 <- appl_34 `pseq` (appl_35 `pseq` klCons appl_34 appl_35)
                                                                                                                                                                                                !appl_37 <- appl_27 `pseq` (appl_36 `pseq` klCons appl_27 appl_36)
                                                                                                                                                                                                !appl_38 <- kl_G `pseq` (appl_37 `pseq` klCons kl_G appl_37)
                                                                                                                                                                                                !appl_39 <- appl_38 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defun")) appl_38
                                                                                                                                                                                                appl_39 `pseq` applyWrapper appl_19 [appl_39])))
                                                                                                                             !appl_40 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                             !appl_41 <- appl_40 `pseq` hd appl_40
                                                                                                                             !appl_42 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                             !appl_43 <- appl_42 `pseq` tl appl_42
                                                                                                                             !appl_44 <- appl_43 `pseq` hd appl_43
                                                                                                                             !appl_45 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                             !appl_46 <- appl_45 `pseq` hd appl_45
                                                                                                                             !appl_47 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                             !appl_48 <- appl_47 `pseq` tl appl_47
                                                                                                                             !appl_49 <- appl_48 `pseq` hd appl_48
                                                                                                                             !appl_50 <- kl_V3969 `pseq` tl kl_V3969
                                                                                                                             !appl_51 <- appl_50 `pseq` tl appl_50
                                                                                                                             !appl_52 <- appl_51 `pseq` hd appl_51
                                                                                                                             !appl_53 <- kl_G `pseq` (appl_52 `pseq` klCons kl_G appl_52)
                                                                                                                             !appl_54 <- appl_46 `pseq` (appl_49 `pseq` (appl_53 `pseq` kl_shen_profile_func appl_46 appl_49 appl_53))
                                                                                                                             let !appl_55 = Atom Nil
                                                                                                                             !appl_56 <- appl_54 `pseq` (appl_55 `pseq` klCons appl_54 appl_55)
                                                                                                                             !appl_57 <- appl_44 `pseq` (appl_56 `pseq` klCons appl_44 appl_56)
                                                                                                                             !appl_58 <- appl_41 `pseq` (appl_57 `pseq` klCons appl_41 appl_57)
                                                                                                                             !appl_59 <- appl_58 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "defun")) appl_58
                                                                                                                             appl_59 `pseq` applyWrapper appl_18 [appl_59])))
                                                                !appl_60 <- kl_gensym (Core.Types.Atom (Core.Types.UnboundSym "shen.f"))
                                                                appl_60 `pseq` applyWrapper appl_17 [appl_60]
                                          Atom (B (False)) -> do do simpleError (Core.Types.Atom (Core.Types.Str "Cannot profile.\n"))
                                          _ -> throwError "if: expected boolean"

kl_unprofile :: Core.Types.KLValue ->
                Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_unprofile (!kl_V3971) = do kl_V3971 `pseq` kl_untrack kl_V3971

kl_shen_profile_func :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_profile_func (!kl_V3975) (!kl_V3976) (!kl_V3977) = do let !appl_0 = Atom Nil
                                                              !appl_1 <- appl_0 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "run")) appl_0
                                                              !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_1
                                                              let !appl_3 = Atom Nil
                                                              !appl_4 <- appl_3 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "run")) appl_3
                                                              !appl_5 <- appl_4 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_4
                                                              let !appl_6 = Atom Nil
                                                              !appl_7 <- appl_6 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Start")) appl_6
                                                              !appl_8 <- appl_5 `pseq` (appl_7 `pseq` klCons appl_5 appl_7)
                                                              !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_8
                                                              let !appl_10 = Atom Nil
                                                              !appl_11 <- kl_V3975 `pseq` (appl_10 `pseq` klCons kl_V3975 appl_10)
                                                              !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "shen.get-profile" kl_shen_get_profile)) appl_11
                                                              let !appl_13 = Atom Nil
                                                              !appl_14 <- appl_13 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Finish")) appl_13
                                                              !appl_15 <- appl_12 `pseq` (appl_14 `pseq` klCons appl_12 appl_14)
                                                              !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_15
                                                              let !appl_17 = Atom Nil
                                                              !appl_18 <- appl_16 `pseq` (appl_17 `pseq` klCons appl_16 appl_17)
                                                              !appl_19 <- kl_V3975 `pseq` (appl_18 `pseq` klCons kl_V3975 appl_18)
                                                              !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "shen.put-profile" kl_shen_put_profile)) appl_19
                                                              let !appl_21 = Atom Nil
                                                              !appl_22 <- appl_21 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_21
                                                              !appl_23 <- appl_20 `pseq` (appl_22 `pseq` klCons appl_20 appl_22)
                                                              !appl_24 <- appl_23 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Record")) appl_23
                                                              !appl_25 <- appl_24 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_24
                                                              let !appl_26 = Atom Nil
                                                              !appl_27 <- appl_25 `pseq` (appl_26 `pseq` klCons appl_25 appl_26)
                                                              !appl_28 <- appl_9 `pseq` (appl_27 `pseq` klCons appl_9 appl_27)
                                                              !appl_29 <- appl_28 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Finish")) appl_28
                                                              !appl_30 <- appl_29 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_29
                                                              let !appl_31 = Atom Nil
                                                              !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                              !appl_33 <- kl_V3977 `pseq` (appl_32 `pseq` klCons kl_V3977 appl_32)
                                                              !appl_34 <- appl_33 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Result")) appl_33
                                                              !appl_35 <- appl_34 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_34
                                                              let !appl_36 = Atom Nil
                                                              !appl_37 <- appl_35 `pseq` (appl_36 `pseq` klCons appl_35 appl_36)
                                                              !appl_38 <- appl_2 `pseq` (appl_37 `pseq` klCons appl_2 appl_37)
                                                              !appl_39 <- appl_38 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "Start")) appl_38
                                                              appl_39 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "let")) appl_39

kl_profile_results :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_profile_results (!kl_V3979) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Results) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Initialise) -> do kl_V3979 `pseq` (kl_Results `pseq` kl_Atp kl_V3979 kl_Results))))
                                                                                                      !appl_2 <- kl_V3979 `pseq` kl_shen_put_profile kl_V3979 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                      appl_2 `pseq` applyWrapper appl_1 [appl_2])))
                                    !appl_3 <- kl_V3979 `pseq` kl_shen_get_profile kl_V3979
                                    appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_get_profile :: Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_get_profile (!kl_V3981) = do let !appl_0 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))))
                                     !appl_1 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                     kl_V3981 `pseq` (appl_0 `pseq` (appl_1 `pseq` kl_getDivor kl_V3981 (ApplC (wrapNamed "profile" kl_profile)) appl_0 appl_1))

kl_shen_put_profile :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_put_profile (!kl_V3984) (!kl_V3985) = do !appl_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "*property-vector*"))
                                                 kl_V3984 `pseq` (kl_V3985 `pseq` (appl_0 `pseq` kl_put kl_V3984 (ApplC (wrapNamed "profile" kl_profile)) kl_V3985 appl_0))

expr7 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr7 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
           (do klSet (Core.Types.Atom (Core.Types.UnboundSym "shen.*step*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
