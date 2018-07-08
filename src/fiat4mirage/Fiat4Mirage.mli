type __ = Obj.t

val negb : bool -> bool

val length : 'a1 list -> int

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

val id : 'a1 -> 'a1

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

val plus : int -> int -> int

val mult : int -> int -> int

val minus : int -> int -> int

val nat_iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

val le_gt_dec : int -> int -> bool

val le_dec : int -> int -> bool

val lt_dec : int -> int -> bool

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> int
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step : (positive -> positive) -> (positive -> positive) -> (positive*mask) -> positive*mask
  
  val sqrtrem : positive -> positive*mask
  
  val sqrt : positive -> positive
  
  val gcdn : int -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn : int -> positive -> positive -> positive*(positive*positive)
  
  val ggcd : positive -> positive -> positive*(positive*positive)
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> int -> positive
  
  val shiftr_nat : positive -> int -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> int -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> int
  
  val of_nat : int -> positive
  
  val of_succ_nat : int -> positive
 end

module Coq_Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> int
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step : (positive -> positive) -> (positive -> positive) -> (positive*mask) -> positive*mask
  
  val sqrtrem : positive -> positive*mask
  
  val sqrt : positive -> positive
  
  val gcdn : int -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn : int -> positive -> positive -> positive*(positive*positive)
  
  val ggcd : positive -> positive -> positive*(positive*positive)
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> int -> positive
  
  val shiftr_nat : positive -> int -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> int -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> int
  
  val of_nat : int -> positive
  
  val of_succ_nat : int -> positive
  
  val eq_dec : positive -> positive -> bool
  
  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  val coq_PeanoView_rect : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec : 'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : positive -> coq_PeanoView
  
  val coq_PeanoView_iter : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val eqb_spec : positive -> positive -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : positive -> positive -> reflect
  
  val ltb_spec0 : positive -> positive -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : positive -> positive -> bool
    
    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case : positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : positive -> positive -> bool
   end
  
  val max_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : positive -> positive -> bool
  
  val min_case_strong : positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : positive -> positive -> bool
 end

module N : 
 sig 
  type t = n
  
  val zero : n
  
  val one : n
  
  val two : n
  
  val succ_double : n -> n
  
  val double : n -> n
  
  val succ : n -> n
  
  val pred : n -> n
  
  val succ_pos : n -> positive
  
  val add : n -> n -> n
  
  val sub : n -> n -> n
  
  val mul : n -> n -> n
  
  val compare : n -> n -> comparison
  
  val eqb : n -> n -> bool
  
  val leb : n -> n -> bool
  
  val ltb : n -> n -> bool
  
  val min : n -> n -> n
  
  val max : n -> n -> n
  
  val div2 : n -> n
  
  val even : n -> bool
  
  val odd : n -> bool
  
  val pow : n -> n -> n
  
  val square : n -> n
  
  val log2 : n -> n
  
  val size : n -> n
  
  val size_nat : n -> int
  
  val pos_div_eucl : positive -> n -> n*n
  
  val div_eucl : n -> n -> n*n
  
  val div : n -> n -> n
  
  val modulo : n -> n -> n
  
  val gcd : n -> n -> n
  
  val ggcd : n -> n -> n*(n*n)
  
  val sqrtrem : n -> n*n
  
  val sqrt : n -> n
  
  val coq_lor : n -> n -> n
  
  val coq_land : n -> n -> n
  
  val ldiff : n -> n -> n
  
  val coq_lxor : n -> n -> n
  
  val shiftl_nat : n -> int -> n
  
  val shiftr_nat : n -> int -> n
  
  val shiftl : n -> n -> n
  
  val shiftr : n -> n -> n
  
  val testbit_nat : n -> int -> bool
  
  val testbit : n -> n -> bool
  
  val to_nat : n -> int
  
  val of_nat : int -> n
  
  val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : n -> n -> bool
  
  val discr : n -> positive option
  
  val binary_rect : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val binary_rec : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val leb_spec0 : n -> n -> reflect
  
  val ltb_spec0 : n -> n -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : n -> n
  
  val log2_up : n -> n
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : n -> n -> n
  
  val eqb_spec : n -> n -> reflect
  
  val b2n : bool -> n
  
  val setbit : n -> n -> n
  
  val clearbit : n -> n -> n
  
  val ones : n -> n
  
  val lnot : n -> n -> n
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : n -> n -> bool
    
    val min_case_strong : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case : n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : n -> n -> bool
   end
  
  val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : n -> n -> bool
  
  val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : n -> n -> bool
 end

module Z : 
 sig 
  type t = z
  
  val zero : z
  
  val one : z
  
  val two : z
  
  val double : z -> z
  
  val succ_double : z -> z
  
  val pred_double : z -> z
  
  val pos_sub : positive -> positive -> z
  
  val add : z -> z -> z
  
  val opp : z -> z
  
  val succ : z -> z
  
  val pred : z -> z
  
  val sub : z -> z -> z
  
  val mul : z -> z -> z
  
  val pow_pos : z -> positive -> z
  
  val pow : z -> z -> z
  
  val square : z -> z
  
  val compare : z -> z -> comparison
  
  val sgn : z -> z
  
  val leb : z -> z -> bool
  
  val ltb : z -> z -> bool
  
  val geb : z -> z -> bool
  
  val gtb : z -> z -> bool
  
  val eqb : z -> z -> bool
  
  val max : z -> z -> z
  
  val min : z -> z -> z
  
  val abs : z -> z
  
  val abs_nat : z -> int
  
  val abs_N : z -> n
  
  val to_nat : z -> int
  
  val to_N : z -> n
  
  val of_nat : int -> z
  
  val of_N : n -> z
  
  val to_pos : z -> positive
  
  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : positive -> z -> z*z
  
  val div_eucl : z -> z -> z*z
  
  val div : z -> z -> z
  
  val modulo : z -> z -> z
  
  val quotrem : z -> z -> z*z
  
  val quot : z -> z -> z
  
  val rem : z -> z -> z
  
  val even : z -> bool
  
  val odd : z -> bool
  
  val div2 : z -> z
  
  val quot2 : z -> z
  
  val log2 : z -> z
  
  val sqrtrem : z -> z*z
  
  val sqrt : z -> z
  
  val gcd : z -> z -> z
  
  val ggcd : z -> z -> z*(z*z)
  
  val testbit : z -> z -> bool
  
  val shiftl : z -> z -> z
  
  val shiftr : z -> z -> z
  
  val coq_lor : z -> z -> z
  
  val coq_land : z -> z -> z
  
  val ldiff : z -> z -> z
  
  val coq_lxor : z -> z -> z
  
  val eq_dec : z -> z -> bool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : z -> z -> reflect
  
  val ltb_spec0 : z -> z -> reflect
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : z -> z
  
  val log2_up : z -> z
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : z -> z -> z
      
      val modulo : z -> z -> z
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : z -> z -> z
  
  val eqb_spec : z -> z -> reflect
  
  val b2z : bool -> z
  
  val setbit : z -> z -> z
  
  val clearbit : z -> z -> z
  
  val lnot : z -> z
  
  val ones : z -> z
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : z -> z -> bool
    
    val min_case_strong : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case : z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : z -> z -> bool
   end
  
  val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : z -> z -> bool
  
  val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : z -> z -> bool
 end

type 'a indexBound =
  ArrayVector.idx_t
  (* singleton inductive, whose constructor was Build_IndexBound *)

val ibound : int -> 'a1 -> 'a1 ArrayVector.storage_t -> 'a1 indexBound -> ArrayVector.idx_t

type 'a boundedIndex = { bindex : 'a; indexb : 'a indexBound }

val bindex : int -> 'a1 ArrayVector.storage_t -> 'a1 boundedIndex -> 'a1

val indexb : int -> 'a1 ArrayVector.storage_t -> 'a1 boundedIndex -> 'a1 indexBound

type 'a enumType = ArrayVector.idx_t

val boundedIndex_inj_EnumType : int -> 'a1 ArrayVector.storage_t -> 'a1 boundedIndex -> 'a1 enumType

type cache =
| Build_Cache

type cacheFormat = __

type cacheDecode = __

type 't cacheAdd = { addE : (cacheFormat -> 't -> cacheFormat); addD : (cacheDecode -> 't -> cacheDecode) }

val addE : cache -> 'a1 cacheAdd -> cacheFormat -> 'a1 -> cacheFormat

val addD : cache -> 'a1 cacheAdd -> cacheDecode -> 'a1 -> cacheDecode

type char = Int64Word.t

val test_cache : cache

val test_cache_add_nat : int cacheAdd

val initialize_Aligned_ByteString : int -> Int64Word.t ArrayVector.storage_t

type w16 = Int64Word.t

val add_bytes_into_checksum : Int64Word.t -> Int64Word.t -> w16 -> Int64Word.t

val vector_checksum' : int -> Int64Word.t ArrayVector.storage_t -> w16

type 'a alignedDecodeM = char ArrayVector.storage_t -> int -> cacheDecode -> (('a*int)*cacheDecode) option

val getCurrentByte : cache -> int cacheAdd -> int -> char alignedDecodeM

val skipCurrentByte : cache -> int cacheAdd -> int -> unit alignedDecodeM

val getCurrentBytes : cache -> int cacheAdd -> int -> int -> Int64Word.t alignedDecodeM

type alignedEncodeM =
  char ArrayVector.storage_t -> int -> cacheFormat -> ((char ArrayVector.storage_t*int)*cacheFormat) option

val setCurrentByte : cache -> int cacheAdd -> int -> char -> alignedEncodeM

val setByteAt : cache -> int cacheAdd -> int -> Int64Word.t -> int -> alignedEncodeM

val alignedEncode_Nil : cache -> int -> alignedEncodeM

val setCurrentBytes : cache -> int cacheAdd -> int -> int -> Int64Word.t -> alignedEncodeM

val calculate_Checksum : cache -> int cacheAdd -> int -> alignedEncodeM

val aligned_decode_enum :
  int -> cache -> int cacheAdd -> Int64Word.t ArrayVector.storage_t -> int -> ArrayVector.idx_t alignedDecodeM

val listAlignedDecodeM : cache -> int -> (int -> 'a1 alignedDecodeM) -> int -> 'a1 list alignedDecodeM

val alignedEncodeList : cache -> ('a1 -> int -> alignedEncodeM) -> 'a1 list -> int -> alignedEncodeM

type iPv4_Packet = { totalLength : Int64Word.t; iD : Int64Word.t; dF : bool; mF : bool;
                     fragmentOffset : Int64Word.t; tTL : Int64Word.t; protocol : char list enumType;
                     sourceAddress : Int64Word.t; destAddress : Int64Word.t; options : Int64Word.t list }

val totalLength : iPv4_Packet -> Int64Word.t

val iD : iPv4_Packet -> Int64Word.t

val dF : iPv4_Packet -> bool

val mF : iPv4_Packet -> bool

val fragmentOffset : iPv4_Packet -> Int64Word.t

val tTL : iPv4_Packet -> Int64Word.t

val protocol : iPv4_Packet -> char list enumType

val sourceAddress : iPv4_Packet -> Int64Word.t

val destAddress : iPv4_Packet -> Int64Word.t

val options : iPv4_Packet -> Int64Word.t list

val protocolTypeCodes : Int64Word.t ArrayVector.storage_t

val iPv4_Packet_Header_Len : iPv4_Packet -> int

val iPv4_encoder_impl :
  iPv4_Packet -> int -> char ArrayVector.storage_t -> ((char ArrayVector.storage_t*int)*cacheFormat) option

val iPv4_decoder_impl : int -> char ArrayVector.storage_t -> ((iPv4_Packet*int)*cacheDecode) option

val bin_pkt : Int64Word.t ArrayVector.storage_t

val pkt : iPv4_Packet

val injectEnum : int -> 'a1 ArrayVector.storage_t -> ArrayVector.idx_t -> 'a1

val makeDecoder :
  int -> (int -> char ArrayVector.storage_t -> (('a1*int)*'a2) option) -> char ArrayVector.storage_t -> 'a1 option

val makeEncoder :
  int -> ('a1 -> int -> char ArrayVector.storage_t -> ((char ArrayVector.storage_t*int)*'a2) option) -> 'a1 -> char
  ArrayVector.storage_t -> char ArrayVector.storage_t option

val fiat_ipv4_decode : int -> char ArrayVector.storage_t -> iPv4_Packet option

type fiat_ipv4_protocol =
| ICMP
| TCP
| UDP

val fiat_ipv4_protocol_to_enum : fiat_ipv4_protocol -> char list enumType

val fiat_ipv4_enum_to_protocol : char list enumType -> fiat_ipv4_protocol

val fiat_ipv4_encode : int -> iPv4_Packet -> char ArrayVector.storage_t -> char ArrayVector.storage_t option

val word_split_hd_test : bool

val word_split_tl_test : int

val alignword_split1'_test : int

val alignword_split2'_test : int

val split1_test : int

val split2_test : int

val combine_test : int

val append_word_test : int

val fiat_ipv4_decode_bench : unit -> iPv4_Packet option

val fiat_ipv4_decode_test : iPv4_Packet option

val fiat_ipv4_decode_reference : iPv4_Packet option

val fiat_ipv4_encode_bench : unit -> char ArrayVector.storage_t option

val fiat_ipv4_encode_test : char ArrayVector.storage_t option

val fiat_ipv4_encode_reference : Int64Word.t ArrayVector.storage_t option

