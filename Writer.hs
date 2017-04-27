{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Writer where

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

kl_pr :: Core.Types.KLValue ->
         Core.Types.KLValue ->
         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_pr (!kl_V4012) (!kl_V4013) = do (do kl_V4012 `pseq` (kl_V4013 `pseq` kl_shen_prh kl_V4012 kl_V4013 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))))) `catchError` (\(!kl_E) -> do return kl_V4012)

kl_shen_prh :: Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_prh (!kl_V4017) (!kl_V4018) (!kl_V4019) = do !appl_0 <- kl_V4017 `pseq` (kl_V4018 `pseq` (kl_V4019 `pseq` kl_shen_write_char_and_inc kl_V4017 kl_V4018 kl_V4019))
                                                     kl_V4017 `pseq` (kl_V4018 `pseq` (appl_0 `pseq` kl_shen_prh kl_V4017 kl_V4018 appl_0))

kl_shen_write_char_and_inc :: Core.Types.KLValue ->
                              Core.Types.KLValue ->
                              Core.Types.KLValue ->
                              Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_write_char_and_inc (!kl_V4023) (!kl_V4024) (!kl_V4025) = do !appl_0 <- kl_V4023 `pseq` (kl_V4025 `pseq` pos kl_V4023 kl_V4025)
                                                                    !appl_1 <- appl_0 `pseq` stringToN appl_0
                                                                    !appl_2 <- appl_1 `pseq` (kl_V4024 `pseq` writeByte appl_1 kl_V4024)
                                                                    !appl_3 <- kl_V4025 `pseq` add kl_V4025 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                    appl_2 `pseq` (appl_3 `pseq` kl_do appl_2 appl_3)

kl_print :: Core.Types.KLValue ->
            Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_print (!kl_V4027) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Print) -> do return kl_V4027)))
                                                                                           !appl_2 <- kl_stoutput
                                                                                           !appl_3 <- kl_String `pseq` (appl_2 `pseq` kl_shen_prhush kl_String appl_2)
                                                                                           appl_3 `pseq` applyWrapper appl_1 [appl_3])))
                          !appl_4 <- kl_V4027 `pseq` kl_shen_insert kl_V4027 (Core.Types.Atom (Core.Types.Str "~S"))
                          appl_4 `pseq` applyWrapper appl_0 [appl_4]

kl_shen_prhush :: Core.Types.KLValue ->
                  Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_prhush (!kl_V4030) (!kl_V4031) = do !kl_if_0 <- value (Core.Types.Atom (Core.Types.UnboundSym "*hush*"))
                                            case kl_if_0 of
                                                Atom (B (True)) -> do return kl_V4030
                                                Atom (B (False)) -> do do kl_V4030 `pseq` (kl_V4031 `pseq` kl_pr kl_V4030 kl_V4031)
                                                _ -> throwError "if: expected boolean"

kl_shen_mkstr :: Core.Types.KLValue ->
                 Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_mkstr (!kl_V4034) (!kl_V4035) = do !kl_if_0 <- kl_V4034 `pseq` stringP kl_V4034
                                           case kl_if_0 of
                                               Atom (B (True)) -> do !appl_1 <- kl_V4034 `pseq` kl_shen_proc_nl kl_V4034
                                                                     appl_1 `pseq` (kl_V4035 `pseq` kl_shen_mkstr_l appl_1 kl_V4035)
                                               Atom (B (False)) -> do do let !appl_2 = Atom Nil
                                                                         !appl_3 <- kl_V4034 `pseq` (appl_2 `pseq` klCons kl_V4034 appl_2)
                                                                         !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl)) appl_3
                                                                         appl_4 `pseq` (kl_V4035 `pseq` kl_shen_mkstr_r appl_4 kl_V4035)
                                               _ -> throwError "if: expected boolean"

kl_shen_mkstr_l :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_mkstr_l (!kl_V4038) (!kl_V4039) = do let !appl_0 = Atom Nil
                                             !kl_if_1 <- appl_0 `pseq` (kl_V4039 `pseq` eq appl_0 kl_V4039)
                                             case kl_if_1 of
                                                 Atom (B (True)) -> do return kl_V4038
                                                 Atom (B (False)) -> do let pat_cond_2 kl_V4039 kl_V4039h kl_V4039t = do !appl_3 <- kl_V4039h `pseq` (kl_V4038 `pseq` kl_shen_insert_l kl_V4039h kl_V4038)
                                                                                                                         appl_3 `pseq` (kl_V4039t `pseq` kl_shen_mkstr_l appl_3 kl_V4039t)
                                                                            pat_cond_4 = do do kl_shen_f_error (ApplC (wrapNamed "shen.mkstr-l" kl_shen_mkstr_l))
                                                                         in case kl_V4039 of
                                                                                !(kl_V4039@(Cons (!kl_V4039h)
                                                                                                 (!kl_V4039t))) -> pat_cond_2 kl_V4039 kl_V4039h kl_V4039t
                                                                                _ -> pat_cond_4
                                                 _ -> throwError "if: expected boolean"

kl_shen_insert_l :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_insert_l (!kl_V4044) (!kl_V4045) = do let pat_cond_0 = do return (Core.Types.Atom (Core.Types.Str ""))
                                                  pat_cond_1 = do !kl_if_2 <- kl_V4045 `pseq` kl_shen_PlusstringP kl_V4045
                                                                  !kl_if_3 <- case kl_if_2 of
                                                                                  Atom (B (True)) -> do !appl_4 <- kl_V4045 `pseq` pos kl_V4045 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                        !kl_if_5 <- appl_4 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_4
                                                                                                        !kl_if_6 <- case kl_if_5 of
                                                                                                                        Atom (B (True)) -> do !appl_7 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                              !kl_if_8 <- appl_7 `pseq` kl_shen_PlusstringP appl_7
                                                                                                                                              !kl_if_9 <- case kl_if_8 of
                                                                                                                                                              Atom (B (True)) -> do !appl_10 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                                                    !appl_11 <- appl_10 `pseq` pos appl_10 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                    !kl_if_12 <- appl_11 `pseq` eq (Core.Types.Atom (Core.Types.Str "A")) appl_11
                                                                                                                                                                                    case kl_if_12 of
                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                              case kl_if_9 of
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
                                                                  case kl_if_3 of
                                                                      Atom (B (True)) -> do !appl_13 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                            !appl_14 <- appl_13 `pseq` tlstr appl_13
                                                                                            let !appl_15 = Atom Nil
                                                                                            !appl_16 <- appl_15 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.a")) appl_15
                                                                                            !appl_17 <- appl_14 `pseq` (appl_16 `pseq` klCons appl_14 appl_16)
                                                                                            !appl_18 <- kl_V4044 `pseq` (appl_17 `pseq` klCons kl_V4044 appl_17)
                                                                                            appl_18 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_18
                                                                      Atom (B (False)) -> do !kl_if_19 <- kl_V4045 `pseq` kl_shen_PlusstringP kl_V4045
                                                                                             !kl_if_20 <- case kl_if_19 of
                                                                                                              Atom (B (True)) -> do !appl_21 <- kl_V4045 `pseq` pos kl_V4045 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                    !kl_if_22 <- appl_21 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_21
                                                                                                                                    !kl_if_23 <- case kl_if_22 of
                                                                                                                                                     Atom (B (True)) -> do !appl_24 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                                           !kl_if_25 <- appl_24 `pseq` kl_shen_PlusstringP appl_24
                                                                                                                                                                           !kl_if_26 <- case kl_if_25 of
                                                                                                                                                                                            Atom (B (True)) -> do !appl_27 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                                                                                  !appl_28 <- appl_27 `pseq` pos appl_27 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                                                  !kl_if_29 <- appl_28 `pseq` eq (Core.Types.Atom (Core.Types.Str "R")) appl_28
                                                                                                                                                                                                                  case kl_if_29 of
                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                           case kl_if_26 of
                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                    case kl_if_23 of
                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                              _ -> throwError "if: expected boolean"
                                                                                             case kl_if_20 of
                                                                                                 Atom (B (True)) -> do !appl_30 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                       !appl_31 <- appl_30 `pseq` tlstr appl_30
                                                                                                                       let !appl_32 = Atom Nil
                                                                                                                       !appl_33 <- appl_32 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.r")) appl_32
                                                                                                                       !appl_34 <- appl_31 `pseq` (appl_33 `pseq` klCons appl_31 appl_33)
                                                                                                                       !appl_35 <- kl_V4044 `pseq` (appl_34 `pseq` klCons kl_V4044 appl_34)
                                                                                                                       appl_35 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_35
                                                                                                 Atom (B (False)) -> do !kl_if_36 <- kl_V4045 `pseq` kl_shen_PlusstringP kl_V4045
                                                                                                                        !kl_if_37 <- case kl_if_36 of
                                                                                                                                         Atom (B (True)) -> do !appl_38 <- kl_V4045 `pseq` pos kl_V4045 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                               !kl_if_39 <- appl_38 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_38
                                                                                                                                                               !kl_if_40 <- case kl_if_39 of
                                                                                                                                                                                Atom (B (True)) -> do !appl_41 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                                                                      !kl_if_42 <- appl_41 `pseq` kl_shen_PlusstringP appl_41
                                                                                                                                                                                                      !kl_if_43 <- case kl_if_42 of
                                                                                                                                                                                                                       Atom (B (True)) -> do !appl_44 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                                                                                                             !appl_45 <- appl_44 `pseq` pos appl_44 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                                                                             !kl_if_46 <- appl_45 `pseq` eq (Core.Types.Atom (Core.Types.Str "S")) appl_45
                                                                                                                                                                                                                                             case kl_if_46 of
                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                                                      case kl_if_43 of
                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                               case kl_if_40 of
                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                        case kl_if_37 of
                                                                                                                            Atom (B (True)) -> do !appl_47 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                  !appl_48 <- appl_47 `pseq` tlstr appl_47
                                                                                                                                                  let !appl_49 = Atom Nil
                                                                                                                                                  !appl_50 <- appl_49 `pseq` klCons (Core.Types.Atom (Core.Types.UnboundSym "shen.s")) appl_49
                                                                                                                                                  !appl_51 <- appl_48 `pseq` (appl_50 `pseq` klCons appl_48 appl_50)
                                                                                                                                                  !appl_52 <- kl_V4044 `pseq` (appl_51 `pseq` klCons kl_V4044 appl_51)
                                                                                                                                                  appl_52 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_52
                                                                                                                            Atom (B (False)) -> do !kl_if_53 <- kl_V4045 `pseq` kl_shen_PlusstringP kl_V4045
                                                                                                                                                   case kl_if_53 of
                                                                                                                                                       Atom (B (True)) -> do !appl_54 <- kl_V4045 `pseq` pos kl_V4045 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                             !appl_55 <- kl_V4045 `pseq` tlstr kl_V4045
                                                                                                                                                                             !appl_56 <- kl_V4044 `pseq` (appl_55 `pseq` kl_shen_insert_l kl_V4044 appl_55)
                                                                                                                                                                             let !appl_57 = Atom Nil
                                                                                                                                                                             !appl_58 <- appl_56 `pseq` (appl_57 `pseq` klCons appl_56 appl_57)
                                                                                                                                                                             !appl_59 <- appl_54 `pseq` (appl_58 `pseq` klCons appl_54 appl_58)
                                                                                                                                                                             !appl_60 <- appl_59 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_59
                                                                                                                                                                             appl_60 `pseq` kl_shen_factor_cn appl_60
                                                                                                                                                       Atom (B (False)) -> do !kl_if_61 <- let pat_cond_62 kl_V4045 kl_V4045h kl_V4045t = do !kl_if_63 <- let pat_cond_64 = do !kl_if_65 <- let pat_cond_66 kl_V4045t kl_V4045th kl_V4045tt = do !kl_if_67 <- let pat_cond_68 kl_V4045tt kl_V4045tth kl_V4045ttt = do let !appl_69 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                      !kl_if_70 <- appl_69 `pseq` (kl_V4045ttt `pseq` eq appl_69 kl_V4045ttt)
                                                                                                                                                                                                                                                                                                                                                                                                                      case kl_if_70 of
                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                  pat_cond_71 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                               in case kl_V4045tt of
                                                                                                                                                                                                                                                                                                                                                                      !(kl_V4045tt@(Cons (!kl_V4045tth)
                                                                                                                                                                                                                                                                                                                                                                                         (!kl_V4045ttt))) -> pat_cond_68 kl_V4045tt kl_V4045tth kl_V4045ttt
                                                                                                                                                                                                                                                                                                                                                                      _ -> pat_cond_71
                                                                                                                                                                                                                                                                                                                                                 case kl_if_67 of
                                                                                                                                                                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                pat_cond_72 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                             in case kl_V4045t of
                                                                                                                                                                                                                                                                                                    !(kl_V4045t@(Cons (!kl_V4045th)
                                                                                                                                                                                                                                                                                                                      (!kl_V4045tt))) -> pat_cond_66 kl_V4045t kl_V4045th kl_V4045tt
                                                                                                                                                                                                                                                                                                    _ -> pat_cond_72
                                                                                                                                                                                                                                                                               case kl_if_65 of
                                                                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                              pat_cond_73 = do do return (Atom (B False))
                                                                                                                                                                                                                                                           in case kl_V4045h of
                                                                                                                                                                                                                                                                  kl_V4045h@(Atom (UnboundSym "cn")) -> pat_cond_64
                                                                                                                                                                                                                                                                  kl_V4045h@(ApplC (PL "cn"
                                                                                                                                                                                                                                                                                       _)) -> pat_cond_64
                                                                                                                                                                                                                                                                  kl_V4045h@(ApplC (Func "cn"
                                                                                                                                                                                                                                                                                         _)) -> pat_cond_64
                                                                                                                                                                                                                                                                  _ -> pat_cond_73
                                                                                                                                                                                                                                             case kl_if_63 of
                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                               pat_cond_74 = do do return (Atom (B False))
                                                                                                                                                                                            in case kl_V4045 of
                                                                                                                                                                                                   !(kl_V4045@(Cons (!kl_V4045h)
                                                                                                                                                                                                                    (!kl_V4045t))) -> pat_cond_62 kl_V4045 kl_V4045h kl_V4045t
                                                                                                                                                                                                   _ -> pat_cond_74
                                                                                                                                                                              case kl_if_61 of
                                                                                                                                                                                  Atom (B (True)) -> do !appl_75 <- kl_V4045 `pseq` tl kl_V4045
                                                                                                                                                                                                        !appl_76 <- appl_75 `pseq` hd appl_75
                                                                                                                                                                                                        !appl_77 <- kl_V4045 `pseq` tl kl_V4045
                                                                                                                                                                                                        !appl_78 <- appl_77 `pseq` tl appl_77
                                                                                                                                                                                                        !appl_79 <- appl_78 `pseq` hd appl_78
                                                                                                                                                                                                        !appl_80 <- kl_V4044 `pseq` (appl_79 `pseq` kl_shen_insert_l kl_V4044 appl_79)
                                                                                                                                                                                                        let !appl_81 = Atom Nil
                                                                                                                                                                                                        !appl_82 <- appl_80 `pseq` (appl_81 `pseq` klCons appl_80 appl_81)
                                                                                                                                                                                                        !appl_83 <- appl_76 `pseq` (appl_82 `pseq` klCons appl_76 appl_82)
                                                                                                                                                                                                        appl_83 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_83
                                                                                                                                                                                  Atom (B (False)) -> do !kl_if_84 <- let pat_cond_85 kl_V4045 kl_V4045h kl_V4045t = do !kl_if_86 <- let pat_cond_87 = do !kl_if_88 <- let pat_cond_89 kl_V4045t kl_V4045th kl_V4045tt = do !kl_if_90 <- let pat_cond_91 kl_V4045tt kl_V4045tth kl_V4045ttt = do !kl_if_92 <- let pat_cond_93 kl_V4045ttt kl_V4045ttth kl_V4045tttt = do let !appl_94 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         !kl_if_95 <- appl_94 `pseq` (kl_V4045tttt `pseq` eq appl_94 kl_V4045tttt)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         case kl_if_95 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  pat_cond_96 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                               in case kl_V4045ttt of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      !(kl_V4045ttt@(Cons (!kl_V4045ttth)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (!kl_V4045tttt))) -> pat_cond_93 kl_V4045ttt kl_V4045ttth kl_V4045tttt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      _ -> pat_cond_96
                                                                                                                                                                                                                                                                                                                                                                                                                                                 case kl_if_92 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                             pat_cond_97 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                          in case kl_V4045tt of
                                                                                                                                                                                                                                                                                                                                                                                                 !(kl_V4045tt@(Cons (!kl_V4045tth)
                                                                                                                                                                                                                                                                                                                                                                                                                    (!kl_V4045ttt))) -> pat_cond_91 kl_V4045tt kl_V4045tth kl_V4045ttt
                                                                                                                                                                                                                                                                                                                                                                                                 _ -> pat_cond_97
                                                                                                                                                                                                                                                                                                                                                                            case kl_if_90 of
                                                                                                                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                           pat_cond_98 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                        in case kl_V4045t of
                                                                                                                                                                                                                                                                                                                               !(kl_V4045t@(Cons (!kl_V4045th)
                                                                                                                                                                                                                                                                                                                                                 (!kl_V4045tt))) -> pat_cond_89 kl_V4045t kl_V4045th kl_V4045tt
                                                                                                                                                                                                                                                                                                                               _ -> pat_cond_98
                                                                                                                                                                                                                                                                                                          case kl_if_88 of
                                                                                                                                                                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                         pat_cond_99 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                      in case kl_V4045h of
                                                                                                                                                                                                                                                                                             kl_V4045h@(Atom (UnboundSym "shen.app")) -> pat_cond_87
                                                                                                                                                                                                                                                                                             kl_V4045h@(ApplC (PL "shen.app"
                                                                                                                                                                                                                                                                                                                  _)) -> pat_cond_87
                                                                                                                                                                                                                                                                                             kl_V4045h@(ApplC (Func "shen.app"
                                                                                                                                                                                                                                                                                                                    _)) -> pat_cond_87
                                                                                                                                                                                                                                                                                             _ -> pat_cond_99
                                                                                                                                                                                                                                                                        case kl_if_86 of
                                                                                                                                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                          pat_cond_100 = do do return (Atom (B False))
                                                                                                                                                                                                                       in case kl_V4045 of
                                                                                                                                                                                                                              !(kl_V4045@(Cons (!kl_V4045h)
                                                                                                                                                                                                                                               (!kl_V4045t))) -> pat_cond_85 kl_V4045 kl_V4045h kl_V4045t
                                                                                                                                                                                                                              _ -> pat_cond_100
                                                                                                                                                                                                         case kl_if_84 of
                                                                                                                                                                                                             Atom (B (True)) -> do !appl_101 <- kl_V4045 `pseq` tl kl_V4045
                                                                                                                                                                                                                                   !appl_102 <- appl_101 `pseq` hd appl_101
                                                                                                                                                                                                                                   !appl_103 <- kl_V4045 `pseq` tl kl_V4045
                                                                                                                                                                                                                                   !appl_104 <- appl_103 `pseq` tl appl_103
                                                                                                                                                                                                                                   !appl_105 <- appl_104 `pseq` hd appl_104
                                                                                                                                                                                                                                   !appl_106 <- kl_V4044 `pseq` (appl_105 `pseq` kl_shen_insert_l kl_V4044 appl_105)
                                                                                                                                                                                                                                   !appl_107 <- kl_V4045 `pseq` tl kl_V4045
                                                                                                                                                                                                                                   !appl_108 <- appl_107 `pseq` tl appl_107
                                                                                                                                                                                                                                   !appl_109 <- appl_108 `pseq` tl appl_108
                                                                                                                                                                                                                                   !appl_110 <- appl_106 `pseq` (appl_109 `pseq` klCons appl_106 appl_109)
                                                                                                                                                                                                                                   !appl_111 <- appl_102 `pseq` (appl_110 `pseq` klCons appl_102 appl_110)
                                                                                                                                                                                                                                   appl_111 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_111
                                                                                                                                                                                                             Atom (B (False)) -> do do kl_shen_f_error (ApplC (wrapNamed "shen.insert-l" kl_shen_insert_l))
                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                 _ -> throwError "if: expected boolean"
                                                                      _ -> throwError "if: expected boolean"
                                               in case kl_V4045 of
                                                      kl_V4045@(Atom (Str "")) -> pat_cond_0
                                                      _ -> pat_cond_1

kl_shen_factor_cn :: Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_factor_cn (!kl_V4047) = do !kl_if_0 <- let pat_cond_1 kl_V4047 kl_V4047h kl_V4047t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V4047t kl_V4047th kl_V4047tt = do !kl_if_6 <- let pat_cond_7 kl_V4047tt kl_V4047tth kl_V4047ttt = do !kl_if_8 <- let pat_cond_9 kl_V4047tth kl_V4047tthh kl_V4047ttht = do !kl_if_10 <- let pat_cond_11 = do !kl_if_12 <- let pat_cond_13 kl_V4047ttht kl_V4047tthth kl_V4047tthtt = do !kl_if_14 <- let pat_cond_15 kl_V4047tthtt kl_V4047tthtth kl_V4047tthttt = do let !appl_16 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    !kl_if_17 <- appl_16 `pseq` (kl_V4047tthttt `pseq` eq appl_16 kl_V4047tthttt)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    !kl_if_18 <- case kl_if_17 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Atom (B (True)) -> do let !appl_19 = Atom Nil
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !kl_if_20 <- appl_19 `pseq` (kl_V4047ttt `pseq` eq appl_19 kl_V4047ttt)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !kl_if_21 <- case kl_if_20 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Atom (B (True)) -> do !kl_if_22 <- kl_V4047th `pseq` stringP kl_V4047th
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  !kl_if_23 <- case kl_if_22 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Atom (B (True)) -> do !kl_if_24 <- kl_V4047tthth `pseq` stringP kl_V4047tthth
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         case kl_if_24 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  case kl_if_23 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           case kl_if_21 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    case kl_if_18 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       pat_cond_25 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    in case kl_V4047tthtt of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !(kl_V4047tthtt@(Cons (!kl_V4047tthtth)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (!kl_V4047tthttt))) -> pat_cond_15 kl_V4047tthtt kl_V4047tthtth kl_V4047tthttt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           _ -> pat_cond_25
                                                                                                                                                                                                                                                                                                                                                                                                                                                      case kl_if_14 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                            pat_cond_26 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                         in case kl_V4047ttht of
                                                                                                                                                                                                                                                                                                                                                                                                !(kl_V4047ttht@(Cons (!kl_V4047tthth)
                                                                                                                                                                                                                                                                                                                                                                                                                     (!kl_V4047tthtt))) -> pat_cond_13 kl_V4047ttht kl_V4047tthth kl_V4047tthtt
                                                                                                                                                                                                                                                                                                                                                                                                _ -> pat_cond_26
                                                                                                                                                                                                                                                                                                                                                                           case kl_if_12 of
                                                                                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                          pat_cond_27 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                       in case kl_V4047tthh of
                                                                                                                                                                                                                                                                                                                                                              kl_V4047tthh@(Atom (UnboundSym "cn")) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                                              kl_V4047tthh@(ApplC (PL "cn"
                                                                                                                                                                                                                                                                                                                                                                                      _)) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                                              kl_V4047tthh@(ApplC (Func "cn"
                                                                                                                                                                                                                                                                                                                                                                                        _)) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                                              _ -> pat_cond_27
                                                                                                                                                                                                                                                                                                                                         case kl_if_10 of
                                                                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                   pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                in case kl_V4047tth of
                                                                                                                                                                                                                                                                                       !(kl_V4047tth@(Cons (!kl_V4047tthh)
                                                                                                                                                                                                                                                                                                           (!kl_V4047ttht))) -> pat_cond_9 kl_V4047tth kl_V4047tthh kl_V4047ttht
                                                                                                                                                                                                                                                                                       _ -> pat_cond_28
                                                                                                                                                                                                                                                                   case kl_if_8 of
                                                                                                                                                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                pat_cond_29 = do do return (Atom (B False))
                                                                                                                                                                                                             in case kl_V4047tt of
                                                                                                                                                                                                                    !(kl_V4047tt@(Cons (!kl_V4047tth)
                                                                                                                                                                                                                                       (!kl_V4047ttt))) -> pat_cond_7 kl_V4047tt kl_V4047tth kl_V4047ttt
                                                                                                                                                                                                                    _ -> pat_cond_29
                                                                                                                                                                                                case kl_if_6 of
                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                pat_cond_30 = do do return (Atom (B False))
                                                                                                                                             in case kl_V4047t of
                                                                                                                                                    !(kl_V4047t@(Cons (!kl_V4047th)
                                                                                                                                                                      (!kl_V4047tt))) -> pat_cond_5 kl_V4047t kl_V4047th kl_V4047tt
                                                                                                                                                    _ -> pat_cond_30
                                                                                                                                case kl_if_4 of
                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                pat_cond_31 = do do return (Atom (B False))
                                                                                                             in case kl_V4047h of
                                                                                                                    kl_V4047h@(Atom (UnboundSym "cn")) -> pat_cond_3
                                                                                                                    kl_V4047h@(ApplC (PL "cn"
                                                                                                                                         _)) -> pat_cond_3
                                                                                                                    kl_V4047h@(ApplC (Func "cn"
                                                                                                                                           _)) -> pat_cond_3
                                                                                                                    _ -> pat_cond_31
                                                                                                case kl_if_2 of
                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                    _ -> throwError "if: expected boolean"
                                                   pat_cond_32 = do do return (Atom (B False))
                                                in case kl_V4047 of
                                                       !(kl_V4047@(Cons (!kl_V4047h)
                                                                        (!kl_V4047t))) -> pat_cond_1 kl_V4047 kl_V4047h kl_V4047t
                                                       _ -> pat_cond_32
                                   case kl_if_0 of
                                       Atom (B (True)) -> do !appl_33 <- kl_V4047 `pseq` tl kl_V4047
                                                             !appl_34 <- appl_33 `pseq` hd appl_33
                                                             !appl_35 <- kl_V4047 `pseq` tl kl_V4047
                                                             !appl_36 <- appl_35 `pseq` tl appl_35
                                                             !appl_37 <- appl_36 `pseq` hd appl_36
                                                             !appl_38 <- appl_37 `pseq` tl appl_37
                                                             !appl_39 <- appl_38 `pseq` hd appl_38
                                                             !appl_40 <- appl_34 `pseq` (appl_39 `pseq` cn appl_34 appl_39)
                                                             !appl_41 <- kl_V4047 `pseq` tl kl_V4047
                                                             !appl_42 <- appl_41 `pseq` tl appl_41
                                                             !appl_43 <- appl_42 `pseq` hd appl_42
                                                             !appl_44 <- appl_43 `pseq` tl appl_43
                                                             !appl_45 <- appl_44 `pseq` tl appl_44
                                                             !appl_46 <- appl_40 `pseq` (appl_45 `pseq` klCons appl_40 appl_45)
                                                             appl_46 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_46
                                       Atom (B (False)) -> do do return kl_V4047
                                       _ -> throwError "if: expected boolean"

kl_shen_proc_nl :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_proc_nl (!kl_V4049) = do let pat_cond_0 = do return (Core.Types.Atom (Core.Types.Str ""))
                                     pat_cond_1 = do !kl_if_2 <- kl_V4049 `pseq` kl_shen_PlusstringP kl_V4049
                                                     !kl_if_3 <- case kl_if_2 of
                                                                     Atom (B (True)) -> do !appl_4 <- kl_V4049 `pseq` pos kl_V4049 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                           !kl_if_5 <- appl_4 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_4
                                                                                           !kl_if_6 <- case kl_if_5 of
                                                                                                           Atom (B (True)) -> do !appl_7 <- kl_V4049 `pseq` tlstr kl_V4049
                                                                                                                                 !kl_if_8 <- appl_7 `pseq` kl_shen_PlusstringP appl_7
                                                                                                                                 !kl_if_9 <- case kl_if_8 of
                                                                                                                                                 Atom (B (True)) -> do !appl_10 <- kl_V4049 `pseq` tlstr kl_V4049
                                                                                                                                                                       !appl_11 <- appl_10 `pseq` pos appl_10 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                       !kl_if_12 <- appl_11 `pseq` eq (Core.Types.Atom (Core.Types.Str "%")) appl_11
                                                                                                                                                                       case kl_if_12 of
                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                 case kl_if_9 of
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
                                                     case kl_if_3 of
                                                         Atom (B (True)) -> do !appl_13 <- nToString (Core.Types.Atom (Core.Types.N (Core.Types.KI 10)))
                                                                               !appl_14 <- kl_V4049 `pseq` tlstr kl_V4049
                                                                               !appl_15 <- appl_14 `pseq` tlstr appl_14
                                                                               !appl_16 <- appl_15 `pseq` kl_shen_proc_nl appl_15
                                                                               appl_13 `pseq` (appl_16 `pseq` cn appl_13 appl_16)
                                                         Atom (B (False)) -> do !kl_if_17 <- kl_V4049 `pseq` kl_shen_PlusstringP kl_V4049
                                                                                case kl_if_17 of
                                                                                    Atom (B (True)) -> do !appl_18 <- kl_V4049 `pseq` pos kl_V4049 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                          !appl_19 <- kl_V4049 `pseq` tlstr kl_V4049
                                                                                                          !appl_20 <- appl_19 `pseq` kl_shen_proc_nl appl_19
                                                                                                          appl_18 `pseq` (appl_20 `pseq` cn appl_18 appl_20)
                                                                                    Atom (B (False)) -> do do kl_shen_f_error (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl))
                                                                                    _ -> throwError "if: expected boolean"
                                                         _ -> throwError "if: expected boolean"
                                  in case kl_V4049 of
                                         kl_V4049@(Atom (Str "")) -> pat_cond_0
                                         _ -> pat_cond_1

kl_shen_mkstr_r :: Core.Types.KLValue ->
                   Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_mkstr_r (!kl_V4052) (!kl_V4053) = do let !appl_0 = Atom Nil
                                             !kl_if_1 <- appl_0 `pseq` (kl_V4053 `pseq` eq appl_0 kl_V4053)
                                             case kl_if_1 of
                                                 Atom (B (True)) -> do return kl_V4052
                                                 Atom (B (False)) -> do let pat_cond_2 kl_V4053 kl_V4053h kl_V4053t = do let !appl_3 = Atom Nil
                                                                                                                         !appl_4 <- kl_V4052 `pseq` (appl_3 `pseq` klCons kl_V4052 appl_3)
                                                                                                                         !appl_5 <- kl_V4053h `pseq` (appl_4 `pseq` klCons kl_V4053h appl_4)
                                                                                                                         !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "shen.insert" kl_shen_insert)) appl_5
                                                                                                                         appl_6 `pseq` (kl_V4053t `pseq` kl_shen_mkstr_r appl_6 kl_V4053t)
                                                                            pat_cond_7 = do do kl_shen_f_error (ApplC (wrapNamed "shen.mkstr-r" kl_shen_mkstr_r))
                                                                         in case kl_V4053 of
                                                                                !(kl_V4053@(Cons (!kl_V4053h)
                                                                                                 (!kl_V4053t))) -> pat_cond_2 kl_V4053 kl_V4053h kl_V4053t
                                                                                _ -> pat_cond_7
                                                 _ -> throwError "if: expected boolean"

kl_shen_insert :: Core.Types.KLValue ->
                  Core.Types.KLValue ->
                  Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_insert (!kl_V4056) (!kl_V4057) = do kl_V4056 `pseq` (kl_V4057 `pseq` kl_shen_insert_h kl_V4056 kl_V4057 (Core.Types.Atom (Core.Types.Str "")))

kl_shen_insert_h :: Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLValue ->
                    Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_insert_h (!kl_V4063) (!kl_V4064) (!kl_V4065) = do let pat_cond_0 = do return kl_V4065
                                                              pat_cond_1 = do !kl_if_2 <- kl_V4064 `pseq` kl_shen_PlusstringP kl_V4064
                                                                              !kl_if_3 <- case kl_if_2 of
                                                                                              Atom (B (True)) -> do !appl_4 <- kl_V4064 `pseq` pos kl_V4064 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                    !kl_if_5 <- appl_4 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_4
                                                                                                                    !kl_if_6 <- case kl_if_5 of
                                                                                                                                    Atom (B (True)) -> do !appl_7 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                          !kl_if_8 <- appl_7 `pseq` kl_shen_PlusstringP appl_7
                                                                                                                                                          !kl_if_9 <- case kl_if_8 of
                                                                                                                                                                          Atom (B (True)) -> do !appl_10 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                                                                !appl_11 <- appl_10 `pseq` pos appl_10 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                                !kl_if_12 <- appl_11 `pseq` eq (Core.Types.Atom (Core.Types.Str "A")) appl_11
                                                                                                                                                                                                case kl_if_12 of
                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                          case kl_if_9 of
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
                                                                              case kl_if_3 of
                                                                                  Atom (B (True)) -> do !appl_13 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                        !appl_14 <- appl_13 `pseq` tlstr appl_13
                                                                                                        !appl_15 <- kl_V4063 `pseq` (appl_14 `pseq` kl_shen_app kl_V4063 appl_14 (Core.Types.Atom (Core.Types.UnboundSym "shen.a")))
                                                                                                        kl_V4065 `pseq` (appl_15 `pseq` cn kl_V4065 appl_15)
                                                                                  Atom (B (False)) -> do !kl_if_16 <- kl_V4064 `pseq` kl_shen_PlusstringP kl_V4064
                                                                                                         !kl_if_17 <- case kl_if_16 of
                                                                                                                          Atom (B (True)) -> do !appl_18 <- kl_V4064 `pseq` pos kl_V4064 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                !kl_if_19 <- appl_18 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_18
                                                                                                                                                !kl_if_20 <- case kl_if_19 of
                                                                                                                                                                 Atom (B (True)) -> do !appl_21 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                                                       !kl_if_22 <- appl_21 `pseq` kl_shen_PlusstringP appl_21
                                                                                                                                                                                       !kl_if_23 <- case kl_if_22 of
                                                                                                                                                                                                        Atom (B (True)) -> do !appl_24 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                                                                                              !appl_25 <- appl_24 `pseq` pos appl_24 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                                                              !kl_if_26 <- appl_25 `pseq` eq (Core.Types.Atom (Core.Types.Str "R")) appl_25
                                                                                                                                                                                                                              case kl_if_26 of
                                                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                       case kl_if_23 of
                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                case kl_if_20 of
                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                         case kl_if_17 of
                                                                                                             Atom (B (True)) -> do !appl_27 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                   !appl_28 <- appl_27 `pseq` tlstr appl_27
                                                                                                                                   !appl_29 <- kl_V4063 `pseq` (appl_28 `pseq` kl_shen_app kl_V4063 appl_28 (Core.Types.Atom (Core.Types.UnboundSym "shen.r")))
                                                                                                                                   kl_V4065 `pseq` (appl_29 `pseq` cn kl_V4065 appl_29)
                                                                                                             Atom (B (False)) -> do !kl_if_30 <- kl_V4064 `pseq` kl_shen_PlusstringP kl_V4064
                                                                                                                                    !kl_if_31 <- case kl_if_30 of
                                                                                                                                                     Atom (B (True)) -> do !appl_32 <- kl_V4064 `pseq` pos kl_V4064 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                           !kl_if_33 <- appl_32 `pseq` eq (Core.Types.Atom (Core.Types.Str "~")) appl_32
                                                                                                                                                                           !kl_if_34 <- case kl_if_33 of
                                                                                                                                                                                            Atom (B (True)) -> do !appl_35 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                                                                                  !kl_if_36 <- appl_35 `pseq` kl_shen_PlusstringP appl_35
                                                                                                                                                                                                                  !kl_if_37 <- case kl_if_36 of
                                                                                                                                                                                                                                   Atom (B (True)) -> do !appl_38 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                                                                                                                         !appl_39 <- appl_38 `pseq` pos appl_38 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                                                                                         !kl_if_40 <- appl_39 `pseq` eq (Core.Types.Atom (Core.Types.Str "S")) appl_39
                                                                                                                                                                                                                                                         case kl_if_40 of
                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                  case kl_if_37 of
                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                           case kl_if_34 of
                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                    case kl_if_31 of
                                                                                                                                        Atom (B (True)) -> do !appl_41 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                              !appl_42 <- appl_41 `pseq` tlstr appl_41
                                                                                                                                                              !appl_43 <- kl_V4063 `pseq` (appl_42 `pseq` kl_shen_app kl_V4063 appl_42 (Core.Types.Atom (Core.Types.UnboundSym "shen.s")))
                                                                                                                                                              kl_V4065 `pseq` (appl_43 `pseq` cn kl_V4065 appl_43)
                                                                                                                                        Atom (B (False)) -> do !kl_if_44 <- kl_V4064 `pseq` kl_shen_PlusstringP kl_V4064
                                                                                                                                                               case kl_if_44 of
                                                                                                                                                                   Atom (B (True)) -> do !appl_45 <- kl_V4064 `pseq` tlstr kl_V4064
                                                                                                                                                                                         !appl_46 <- kl_V4064 `pseq` pos kl_V4064 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                                                                                                                                         !appl_47 <- kl_V4065 `pseq` (appl_46 `pseq` cn kl_V4065 appl_46)
                                                                                                                                                                                         kl_V4063 `pseq` (appl_45 `pseq` (appl_47 `pseq` kl_shen_insert_h kl_V4063 appl_45 appl_47))
                                                                                                                                                                   Atom (B (False)) -> do do kl_shen_f_error (ApplC (wrapNamed "shen.insert-h" kl_shen_insert_h))
                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                             _ -> throwError "if: expected boolean"
                                                                                  _ -> throwError "if: expected boolean"
                                                           in case kl_V4064 of
                                                                  kl_V4064@(Atom (Str "")) -> pat_cond_0
                                                                  _ -> pat_cond_1

kl_shen_app :: Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLValue ->
               Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_app (!kl_V4069) (!kl_V4070) (!kl_V4071) = do !appl_0 <- kl_V4069 `pseq` (kl_V4071 `pseq` kl_shen_arg_RBstr kl_V4069 kl_V4071)
                                                     appl_0 `pseq` (kl_V4070 `pseq` cn appl_0 kl_V4070)

kl_shen_arg_RBstr :: Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_arg_RBstr (!kl_V4079) (!kl_V4080) = do !appl_0 <- kl_fail
                                               !kl_if_1 <- kl_V4079 `pseq` (appl_0 `pseq` eq kl_V4079 appl_0)
                                               case kl_if_1 of
                                                   Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.Str "..."))
                                                   Atom (B (False)) -> do !kl_if_2 <- kl_V4079 `pseq` kl_shen_listP kl_V4079
                                                                          case kl_if_2 of
                                                                              Atom (B (True)) -> do kl_V4079 `pseq` (kl_V4080 `pseq` kl_shen_list_RBstr kl_V4079 kl_V4080)
                                                                              Atom (B (False)) -> do !kl_if_3 <- kl_V4079 `pseq` stringP kl_V4079
                                                                                                     case kl_if_3 of
                                                                                                         Atom (B (True)) -> do kl_V4079 `pseq` (kl_V4080 `pseq` kl_shen_str_RBstr kl_V4079 kl_V4080)
                                                                                                         Atom (B (False)) -> do !kl_if_4 <- kl_V4079 `pseq` absvectorP kl_V4079
                                                                                                                                case kl_if_4 of
                                                                                                                                    Atom (B (True)) -> do kl_V4079 `pseq` (kl_V4080 `pseq` kl_shen_vector_RBstr kl_V4079 kl_V4080)
                                                                                                                                    Atom (B (False)) -> do do kl_V4079 `pseq` kl_shen_atom_RBstr kl_V4079
                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                         _ -> throwError "if: expected boolean"
                                                                              _ -> throwError "if: expected boolean"
                                                   _ -> throwError "if: expected boolean"

kl_shen_list_RBstr :: Core.Types.KLValue ->
                      Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_list_RBstr (!kl_V4083) (!kl_V4084) = do let pat_cond_0 = do !appl_1 <- kl_shen_maxseq
                                                                    !appl_2 <- kl_V4083 `pseq` (appl_1 `pseq` kl_shen_iter_list kl_V4083 (Core.Types.Atom (Core.Types.UnboundSym "shen.r")) appl_1)
                                                                    !appl_3 <- appl_2 `pseq` kl_Ats appl_2 (Core.Types.Atom (Core.Types.Str ")"))
                                                                    appl_3 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "(")) appl_3
                                                    pat_cond_4 = do do !appl_5 <- kl_shen_maxseq
                                                                       !appl_6 <- kl_V4083 `pseq` (kl_V4084 `pseq` (appl_5 `pseq` kl_shen_iter_list kl_V4083 kl_V4084 appl_5))
                                                                       !appl_7 <- appl_6 `pseq` kl_Ats appl_6 (Core.Types.Atom (Core.Types.Str "]"))
                                                                       appl_7 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "[")) appl_7
                                                 in case kl_V4084 of
                                                        kl_V4084@(Atom (UnboundSym "shen.r")) -> pat_cond_0
                                                        kl_V4084@(ApplC (PL "shen.r"
                                                                            _)) -> pat_cond_0
                                                        kl_V4084@(ApplC (Func "shen.r"
                                                                              _)) -> pat_cond_0
                                                        _ -> pat_cond_4

kl_shen_maxseq :: Core.Types.KLContext Core.Types.Env
                                       Core.Types.KLValue
kl_shen_maxseq = do value (Core.Types.Atom (Core.Types.UnboundSym "*maximum-print-sequence-size*"))

kl_shen_iter_list :: Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_iter_list (!kl_V4098) (!kl_V4099) (!kl_V4100) = do let !appl_0 = Atom Nil
                                                           !kl_if_1 <- appl_0 `pseq` (kl_V4098 `pseq` eq appl_0 kl_V4098)
                                                           case kl_if_1 of
                                                               Atom (B (True)) -> do return (Core.Types.Atom (Core.Types.Str ""))
                                                               Atom (B (False)) -> do let pat_cond_2 = do return (Core.Types.Atom (Core.Types.Str "... etc"))
                                                                                          pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V4098 kl_V4098h kl_V4098t = do let !appl_6 = Atom Nil
                                                                                                                                                                       !kl_if_7 <- appl_6 `pseq` (kl_V4098t `pseq` eq appl_6 kl_V4098t)
                                                                                                                                                                       case kl_if_7 of
                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                          pat_cond_8 = do do return (Atom (B False))
                                                                                                                       in case kl_V4098 of
                                                                                                                              !(kl_V4098@(Cons (!kl_V4098h)
                                                                                                                                               (!kl_V4098t))) -> pat_cond_5 kl_V4098 kl_V4098h kl_V4098t
                                                                                                                              _ -> pat_cond_8
                                                                                                          case kl_if_4 of
                                                                                                              Atom (B (True)) -> do !appl_9 <- kl_V4098 `pseq` hd kl_V4098
                                                                                                                                    appl_9 `pseq` (kl_V4099 `pseq` kl_shen_arg_RBstr appl_9 kl_V4099)
                                                                                                              Atom (B (False)) -> do let pat_cond_10 kl_V4098 kl_V4098h kl_V4098t = do !appl_11 <- kl_V4098h `pseq` (kl_V4099 `pseq` kl_shen_arg_RBstr kl_V4098h kl_V4099)
                                                                                                                                                                                       !appl_12 <- kl_V4100 `pseq` Primitives.subtract kl_V4100 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                                                       !appl_13 <- kl_V4098t `pseq` (kl_V4099 `pseq` (appl_12 `pseq` kl_shen_iter_list kl_V4098t kl_V4099 appl_12))
                                                                                                                                                                                       !appl_14 <- appl_13 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str " ")) appl_13
                                                                                                                                                                                       appl_11 `pseq` (appl_14 `pseq` kl_Ats appl_11 appl_14)
                                                                                                                                         pat_cond_15 = do do !appl_16 <- kl_V4098 `pseq` (kl_V4099 `pseq` kl_shen_arg_RBstr kl_V4098 kl_V4099)
                                                                                                                                                             !appl_17 <- appl_16 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str " ")) appl_16
                                                                                                                                                             appl_17 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "|")) appl_17
                                                                                                                                      in case kl_V4098 of
                                                                                                                                             !(kl_V4098@(Cons (!kl_V4098h)
                                                                                                                                                              (!kl_V4098t))) -> pat_cond_10 kl_V4098 kl_V4098h kl_V4098t
                                                                                                                                             _ -> pat_cond_15
                                                                                                              _ -> throwError "if: expected boolean"
                                                                                       in case kl_V4100 of
                                                                                              kl_V4100@(Atom (N (KI 0))) -> pat_cond_2
                                                                                              _ -> pat_cond_3
                                                               _ -> throwError "if: expected boolean"

kl_shen_str_RBstr :: Core.Types.KLValue ->
                     Core.Types.KLValue ->
                     Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_str_RBstr (!kl_V4107) (!kl_V4108) = do let pat_cond_0 = do return kl_V4107
                                                   pat_cond_1 = do do !appl_2 <- nToString (Core.Types.Atom (Core.Types.N (Core.Types.KI 34)))
                                                                      !appl_3 <- nToString (Core.Types.Atom (Core.Types.N (Core.Types.KI 34)))
                                                                      !appl_4 <- kl_V4107 `pseq` (appl_3 `pseq` kl_Ats kl_V4107 appl_3)
                                                                      appl_2 `pseq` (appl_4 `pseq` kl_Ats appl_2 appl_4)
                                                in case kl_V4108 of
                                                       kl_V4108@(Atom (UnboundSym "shen.a")) -> pat_cond_0
                                                       kl_V4108@(ApplC (PL "shen.a"
                                                                           _)) -> pat_cond_0
                                                       kl_V4108@(ApplC (Func "shen.a"
                                                                             _)) -> pat_cond_0
                                                       _ -> pat_cond_1

kl_shen_vector_RBstr :: Core.Types.KLValue ->
                        Core.Types.KLValue ->
                        Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_vector_RBstr (!kl_V4111) (!kl_V4112) = do !kl_if_0 <- kl_V4111 `pseq` kl_shen_print_vectorP kl_V4111
                                                  case kl_if_0 of
                                                      Atom (B (True)) -> do !appl_1 <- kl_V4111 `pseq` addressFrom kl_V4111 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                                                            !appl_2 <- appl_1 `pseq` kl_function appl_1
                                                                            kl_V4111 `pseq` applyWrapper appl_2 [kl_V4111]
                                                      Atom (B (False)) -> do do !kl_if_3 <- kl_V4111 `pseq` kl_vectorP kl_V4111
                                                                                case kl_if_3 of
                                                                                    Atom (B (True)) -> do !appl_4 <- kl_shen_maxseq
                                                                                                          !appl_5 <- kl_V4111 `pseq` (kl_V4112 `pseq` (appl_4 `pseq` kl_shen_iter_vector kl_V4111 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1))) kl_V4112 appl_4))
                                                                                                          !appl_6 <- appl_5 `pseq` kl_Ats appl_5 (Core.Types.Atom (Core.Types.Str ">"))
                                                                                                          appl_6 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "<")) appl_6
                                                                                    Atom (B (False)) -> do do !appl_7 <- kl_shen_maxseq
                                                                                                              !appl_8 <- kl_V4111 `pseq` (kl_V4112 `pseq` (appl_7 `pseq` kl_shen_iter_vector kl_V4111 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0))) kl_V4112 appl_7))
                                                                                                              !appl_9 <- appl_8 `pseq` kl_Ats appl_8 (Core.Types.Atom (Core.Types.Str ">>"))
                                                                                                              !appl_10 <- appl_9 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "<")) appl_9
                                                                                                              appl_10 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "<")) appl_10
                                                                                    _ -> throwError "if: expected boolean"
                                                      _ -> throwError "if: expected boolean"

kl_shen_print_vectorP :: Core.Types.KLValue ->
                         Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_print_vectorP (!kl_V4114) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Zero) -> do let pat_cond_1 = do return (Atom (B True))
                                                                                                          pat_cond_2 = do do let pat_cond_3 = do return (Atom (B True))
                                                                                                                                 pat_cond_4 = do do let pat_cond_5 = do return (Atom (B True))
                                                                                                                                                        pat_cond_6 = do do !appl_7 <- kl_Zero `pseq` numberP kl_Zero
                                                                                                                                                                           !kl_if_8 <- appl_7 `pseq` kl_not appl_7
                                                                                                                                                                           case kl_if_8 of
                                                                                                                                                                               Atom (B (True)) -> do kl_Zero `pseq` kl_shen_fboundP kl_Zero
                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                     in case kl_Zero of
                                                                                                                                                            kl_Zero@(Atom (UnboundSym "shen.dictionary")) -> pat_cond_5
                                                                                                                                                            kl_Zero@(ApplC (PL "shen.dictionary"
                                                                                                                                                                               _)) -> pat_cond_5
                                                                                                                                                            kl_Zero@(ApplC (Func "shen.dictionary"
                                                                                                                                                                                 _)) -> pat_cond_5
                                                                                                                                                            _ -> pat_cond_6
                                                                                                                              in case kl_Zero of
                                                                                                                                     kl_Zero@(Atom (UnboundSym "shen.pvar")) -> pat_cond_3
                                                                                                                                     kl_Zero@(ApplC (PL "shen.pvar"
                                                                                                                                                        _)) -> pat_cond_3
                                                                                                                                     kl_Zero@(ApplC (Func "shen.pvar"
                                                                                                                                                          _)) -> pat_cond_3
                                                                                                                                     _ -> pat_cond_4
                                                                                                       in case kl_Zero of
                                                                                                              kl_Zero@(Atom (UnboundSym "shen.tuple")) -> pat_cond_1
                                                                                                              kl_Zero@(ApplC (PL "shen.tuple"
                                                                                                                                 _)) -> pat_cond_1
                                                                                                              kl_Zero@(ApplC (Func "shen.tuple"
                                                                                                                                   _)) -> pat_cond_1
                                                                                                              _ -> pat_cond_2)))
                                       !appl_9 <- kl_V4114 `pseq` addressFrom kl_V4114 (Core.Types.Atom (Core.Types.N (Core.Types.KI 0)))
                                       appl_9 `pseq` applyWrapper appl_0 [appl_9]

kl_shen_fboundP :: Core.Types.KLValue ->
                   Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_fboundP (!kl_V4116) = do (do !appl_0 <- kl_V4116 `pseq` kl_shen_lookup_func kl_V4116
                                     appl_0 `pseq` kl_do appl_0 (Atom (B True))) `catchError` (\(!kl_E) -> do return (Atom (B False)))

kl_shen_tuple :: Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_tuple (!kl_V4118) = do !appl_0 <- kl_V4118 `pseq` addressFrom kl_V4118 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                               !appl_1 <- kl_V4118 `pseq` addressFrom kl_V4118 (Core.Types.Atom (Core.Types.N (Core.Types.KI 2)))
                               !appl_2 <- appl_1 `pseq` kl_shen_app appl_1 (Core.Types.Atom (Core.Types.Str ")")) (Core.Types.Atom (Core.Types.UnboundSym "shen.s"))
                               !appl_3 <- appl_2 `pseq` cn (Core.Types.Atom (Core.Types.Str " ")) appl_2
                               !appl_4 <- appl_0 `pseq` (appl_3 `pseq` kl_shen_app appl_0 appl_3 (Core.Types.Atom (Core.Types.UnboundSym "shen.s")))
                               appl_4 `pseq` cn (Core.Types.Atom (Core.Types.Str "(@p ")) appl_4

kl_shen_dictionary :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_dictionary (!kl_V4120) = do return (Core.Types.Atom (Core.Types.Str "(dict ...)"))

kl_shen_iter_vector :: Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLValue ->
                       Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_iter_vector (!kl_V4131) (!kl_V4132) (!kl_V4133) (!kl_V4134) = do let pat_cond_0 = do return (Core.Types.Atom (Core.Types.Str "... etc"))
                                                                             pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Item) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Next) -> do let pat_cond_4 = do return (Core.Types.Atom (Core.Types.Str ""))
                                                                                                                                                                                                                                  pat_cond_5 = do do let pat_cond_6 = do kl_Item `pseq` (kl_V4133 `pseq` kl_shen_arg_RBstr kl_Item kl_V4133)
                                                                                                                                                                                                                                                         pat_cond_7 = do do !appl_8 <- kl_Item `pseq` (kl_V4133 `pseq` kl_shen_arg_RBstr kl_Item kl_V4133)
                                                                                                                                                                                                                                                                            !appl_9 <- kl_V4132 `pseq` add kl_V4132 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                                                                                                                                            !appl_10 <- kl_V4134 `pseq` Primitives.subtract kl_V4134 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                                                                                                                                            !appl_11 <- kl_V4131 `pseq` (appl_9 `pseq` (kl_V4133 `pseq` (appl_10 `pseq` kl_shen_iter_vector kl_V4131 appl_9 kl_V4133 appl_10)))
                                                                                                                                                                                                                                                                            !appl_12 <- appl_11 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str " ")) appl_11
                                                                                                                                                                                                                                                                            appl_8 `pseq` (appl_12 `pseq` kl_Ats appl_8 appl_12)
                                                                                                                                                                                                                                                      in case kl_Next of
                                                                                                                                                                                                                                                             kl_Next@(Atom (UnboundSym "shen.out-of-bounds")) -> pat_cond_6
                                                                                                                                                                                                                                                             kl_Next@(ApplC (PL "shen.out-of-bounds"
                                                                                                                                                                                                                                                                                _)) -> pat_cond_6
                                                                                                                                                                                                                                                             kl_Next@(ApplC (Func "shen.out-of-bounds"
                                                                                                                                                                                                                                                                                  _)) -> pat_cond_6
                                                                                                                                                                                                                                                             _ -> pat_cond_7
                                                                                                                                                                                                                               in case kl_Item of
                                                                                                                                                                                                                                      kl_Item@(Atom (UnboundSym "shen.out-of-bounds")) -> pat_cond_4
                                                                                                                                                                                                                                      kl_Item@(ApplC (PL "shen.out-of-bounds"
                                                                                                                                                                                                                                                         _)) -> pat_cond_4
                                                                                                                                                                                                                                      kl_Item@(ApplC (Func "shen.out-of-bounds"
                                                                                                                                                                                                                                                           _)) -> pat_cond_4
                                                                                                                                                                                                                                      _ -> pat_cond_5)))
                                                                                                                                                               !appl_13 <- kl_V4132 `pseq` add kl_V4132 (Core.Types.Atom (Core.Types.N (Core.Types.KI 1)))
                                                                                                                                                               let !appl_14 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.UnboundSym "shen.out-of-bounds"))))
                                                                                                                                                               !appl_15 <- kl_V4131 `pseq` (appl_13 `pseq` (appl_14 `pseq` kl_LB_addressDivor kl_V4131 appl_13 appl_14))
                                                                                                                                                               appl_15 `pseq` applyWrapper appl_3 [appl_15])))
                                                                                                let !appl_16 = ApplC (PL "thunk" (do return (Core.Types.Atom (Core.Types.UnboundSym "shen.out-of-bounds"))))
                                                                                                !appl_17 <- kl_V4131 `pseq` (kl_V4132 `pseq` (appl_16 `pseq` kl_LB_addressDivor kl_V4131 kl_V4132 appl_16))
                                                                                                appl_17 `pseq` applyWrapper appl_2 [appl_17]
                                                                          in case kl_V4134 of
                                                                                 kl_V4134@(Atom (N (KI 0))) -> pat_cond_0
                                                                                 _ -> pat_cond_1

kl_shen_atom_RBstr :: Core.Types.KLValue ->
                      Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_atom_RBstr (!kl_V4136) = do (do kl_V4136 `pseq` str kl_V4136) `catchError` (\(!kl_E) -> do kl_shen_funexstring)

kl_shen_funexstring :: Core.Types.KLContext Core.Types.Env
                                            Core.Types.KLValue
kl_shen_funexstring = do !appl_0 <- intern (Core.Types.Atom (Core.Types.Str "x"))
                         !appl_1 <- appl_0 `pseq` kl_gensym appl_0
                         !appl_2 <- appl_1 `pseq` kl_shen_arg_RBstr appl_1 (Core.Types.Atom (Core.Types.UnboundSym "shen.a"))
                         !appl_3 <- appl_2 `pseq` kl_Ats appl_2 (Core.Types.Atom (Core.Types.Str "\\DC1"))
                         !appl_4 <- appl_3 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "e")) appl_3
                         !appl_5 <- appl_4 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "n")) appl_4
                         !appl_6 <- appl_5 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "u")) appl_5
                         !appl_7 <- appl_6 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "f")) appl_6
                         appl_7 `pseq` kl_Ats (Core.Types.Atom (Core.Types.Str "\\DLE")) appl_7

kl_shen_listP :: Core.Types.KLValue ->
                 Core.Types.KLContext Core.Types.Env Core.Types.KLValue
kl_shen_listP (!kl_V4138) = do !kl_if_0 <- kl_V4138 `pseq` kl_emptyP kl_V4138
                               case kl_if_0 of
                                   Atom (B (True)) -> do return (Atom (B True))
                                   Atom (B (False)) -> do do let pat_cond_1 kl_V4138 kl_V4138h kl_V4138t = do return (Atom (B True))
                                                                 pat_cond_2 = do do return (Atom (B False))
                                                              in case kl_V4138 of
                                                                     !(kl_V4138@(Cons (!kl_V4138h)
                                                                                      (!kl_V4138t))) -> pat_cond_1 kl_V4138 kl_V4138h kl_V4138t
                                                                     _ -> pat_cond_2
                                   _ -> throwError "if: expected boolean"

expr9 :: Core.Types.KLContext Core.Types.Env Core.Types.KLValue
expr9 = do (do return (Core.Types.Atom (Core.Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Core.Types.Atom (Core.Types.Str "E")))
