/* Generated by CIL v. 1.5.1 */
/* print_CIL_Input is false */

#line 40 "/usr/lib/gcc/x86_64-linux-gnu/4.6/include/stdarg.h"
typedef __builtin_va_list __gnuc_va_list[1U];
#line 102 "/usr/lib/gcc/x86_64-linux-gnu/4.6/include/stdarg.h"
typedef __gnuc_va_list va_list[1U];
#line 11 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/posix_types_64.h"
typedef unsigned int __kernel_mode_t;
#line 18 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/posix_types_64.h"
typedef unsigned long __kernel_size_t;
#line 19 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/posix_types_64.h"
typedef long __kernel_ssize_t;
#line 32 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/posix_types_64.h"
typedef long long __kernel_loff_t;
#line 18 "include/asm-generic/int-ll64.h"
typedef unsigned char __u8;
#line 21 "include/asm-generic/int-ll64.h"
typedef unsigned short __u16;
#line 24 "include/asm-generic/int-ll64.h"
typedef unsigned int __u32;
#line 28 "include/asm-generic/int-ll64.h"
typedef unsigned long long __u64;
#line 50 "include/asm-generic/int-ll64.h"
typedef unsigned long long u64;
#line 21 "include/linux/types.h"
typedef __kernel_mode_t mode_t;
#line 57 "include/linux/types.h"
typedef __kernel_loff_t loff_t;
#line 66 "include/linux/types.h"
typedef __kernel_size_t size_t;
#line 71 "include/linux/types.h"
typedef __kernel_ssize_t ssize_t;
#line 95 "include/linux/types.h"
typedef unsigned char u_char;
#line 98 "include/linux/types.h"
typedef unsigned long u_long;
#line 118 "include/linux/types.h"
typedef __u8 uint8_t;
#line 120 "include/linux/types.h"
typedef __u32 uint32_t;
#line 123 "include/linux/types.h"
typedef __u64 uint64_t;
#line 186 "include/linux/types.h"
typedef unsigned int gfp_t;
#line 190 "include/linux/types.h"
typedef u64 phys_addr_t;
#line 195 "include/linux/types.h"
typedef phys_addr_t resource_size_t;
#line 199 "include/linux/types.h"
struct __anonstruct_atomic_t_6 {
   int volatile   counter ;
};
#line 199 "include/linux/types.h"
typedef struct __anonstruct_atomic_t_6 atomic_t;
#line 204 "include/linux/types.h"
struct __anonstruct_atomic64_t_7 {
   long volatile   counter ;
};
#line 204 "include/linux/types.h"
typedef struct __anonstruct_atomic64_t_7 atomic64_t;
#line 58 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/alternative.h"
struct module;
#line 37 "include/linux/dynamic_printk.h"
struct bug_entry {
   int bug_addr_disp ;
   int file_disp ;
   unsigned short line ;
   unsigned short flags ;
};
#line 83 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/page_64.h"
struct page;
#line 324 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/paravirt.h"
struct raw_spinlock;
#line 21 "include/asm-generic/page.h"
struct task_struct;
#line 386 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/processor.h"
struct kmem_cache;
#line 23 "include/asm-generic/atomic.h"
typedef atomic64_t atomic_long_t;
#line 56 "include/linux/prefetch.h"
struct list_head {
   struct list_head *next ;
   struct list_head *prev ;
};
#line 8 "include/linux/bottom_half.h"
struct raw_spinlock {
   unsigned int slock ;
};
#line 10 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/spinlock_types.h"
typedef struct raw_spinlock raw_spinlock_t;
#line 17
struct lockdep_map;
#line 48 "include/linux/debug_locks.h"
struct stack_trace {
   unsigned int nr_entries ;
   unsigned int max_entries ;
   unsigned long *entries ;
   int skip ;
};
#line 34 "include/linux/stacktrace.h"
struct lockdep_subclass_key {
   char __one_byte ;
};
#line 71 "include/linux/lockdep.h"
struct lock_class_key {
   struct lockdep_subclass_key subkeys[8U] ;
};
#line 75 "include/linux/lockdep.h"
struct lock_class {
   struct list_head hash_entry ;
   struct list_head lock_entry ;
   struct lockdep_subclass_key *key ;
   unsigned int subclass ;
   unsigned int dep_gen_id ;
   unsigned long usage_mask ;
   struct stack_trace usage_traces[9U] ;
   struct list_head locks_after ;
   struct list_head locks_before ;
   unsigned int version ;
   unsigned long ops ;
   char const   *name ;
   int name_version ;
   unsigned long contention_point[4U] ;
   unsigned long contending_point[4U] ;
};
#line 160 "include/linux/lockdep.h"
struct lockdep_map {
   struct lock_class_key *key ;
   struct lock_class *class_cache ;
   char const   *name ;
   int cpu ;
   unsigned long ip ;
};
#line 32 "include/linux/spinlock_types.h"
struct __anonstruct_spinlock_t_32 {
   raw_spinlock_t raw_lock ;
   unsigned int magic ;
   unsigned int owner_cpu ;
   void *owner ;
   struct lockdep_map dep_map ;
};
#line 32 "include/linux/spinlock_types.h"
typedef struct __anonstruct_spinlock_t_32 spinlock_t;
#line 52 "include/linux/srcu.h"
struct notifier_block {
   int (*notifier_call)(struct notifier_block * , unsigned long  , void * ) ;
   struct notifier_block *next ;
   int priority ;
};
#line 262 "include/linux/workqueue.h"
struct kobject;
#line 263 "include/linux/workqueue.h"
struct attribute {
   char const   *name ;
   struct module *owner ;
   mode_t mode ;
};
#line 75 "include/linux/sysfs.h"
struct sysfs_ops {
   ssize_t (*show)(struct kobject * , struct attribute * , char * ) ;
   ssize_t (*store)(struct kobject * , struct attribute * , char const   * , size_t  ) ;
};
#line 81
struct sysfs_dirent;
#line 131 "include/linux/sysfs.h"
struct kref {
   atomic_t refcount ;
};
#line 48 "include/linux/kobject.h"
struct kset;
#line 48
struct kobj_type;
#line 48 "include/linux/kobject.h"
struct kobject {
   char const   *name ;
   struct list_head entry ;
   struct kobject *parent ;
   struct kset *kset ;
   struct kobj_type *ktype ;
   struct sysfs_dirent *sd ;
   struct kref kref ;
   unsigned char state_initialized : 1 ;
   unsigned char state_in_sysfs : 1 ;
   unsigned char state_add_uevent_sent : 1 ;
   unsigned char state_remove_uevent_sent : 1 ;
};
#line 103 "include/linux/kobject.h"
struct kobj_type {
   void (*release)(struct kobject * ) ;
   struct sysfs_ops *sysfs_ops ;
   struct attribute **default_attrs ;
};
#line 109 "include/linux/kobject.h"
struct kobj_uevent_env {
   char *envp[32U] ;
   int envp_idx ;
   char buf[2048U] ;
   int buflen ;
};
#line 116 "include/linux/kobject.h"
struct kset_uevent_ops {
   int (*filter)(struct kset * , struct kobject * ) ;
   char const   *(*name)(struct kset * , struct kobject * ) ;
   int (*uevent)(struct kset * , struct kobject * , struct kobj_uevent_env * ) ;
};
#line 133 "include/linux/kobject.h"
struct kset {
   struct list_head list ;
   spinlock_t list_lock ;
   struct kobject kobj ;
   struct kset_uevent_ops *uevent_ops ;
};
#line 229 "include/linux/kobject.h"
struct kmem_cache_cpu {
   void **freelist ;
   struct page *page ;
   int node ;
   unsigned int offset ;
   unsigned int objsize ;
   unsigned int stat[18U] ;
};
#line 44 "include/linux/slub_def.h"
struct kmem_cache_node {
   spinlock_t list_lock ;
   unsigned long nr_partial ;
   unsigned long min_partial ;
   struct list_head partial ;
   atomic_long_t nr_slabs ;
   atomic_long_t total_objects ;
   struct list_head full ;
};
#line 56 "include/linux/slub_def.h"
struct kmem_cache_order_objects {
   unsigned long x ;
};
#line 66 "include/linux/slub_def.h"
struct kmem_cache {
   unsigned long flags ;
   int size ;
   int objsize ;
   int offset ;
   struct kmem_cache_order_objects oo ;
   struct kmem_cache_node local_node ;
   struct kmem_cache_order_objects max ;
   struct kmem_cache_order_objects min ;
   gfp_t allocflags ;
   int refcount ;
   void (*ctor)(void * ) ;
   int inuse ;
   int align ;
   char const   *name ;
   struct list_head list ;
   struct kobject kobj ;
   int remote_node_defrag_ratio ;
   struct kmem_cache_node *node[512U] ;
   struct kmem_cache_cpu *cpu_slab[4096U] ;
};
#line 27 "include/linux/elf.h"
typedef __u64 Elf64_Addr;
#line 28 "include/linux/elf.h"
typedef __u16 Elf64_Half;
#line 32 "include/linux/elf.h"
typedef __u32 Elf64_Word;
#line 33 "include/linux/elf.h"
typedef __u64 Elf64_Xword;
#line 180 "include/linux/elf.h"
struct elf64_sym {
   Elf64_Word st_name ;
   unsigned char st_info ;
   unsigned char st_other ;
   Elf64_Half st_shndx ;
   Elf64_Addr st_value ;
   Elf64_Xword st_size ;
};
#line 188 "include/linux/elf.h"
typedef struct elf64_sym Elf64_Sym;
#line 215 "include/linux/moduleparam.h"
struct marker;
#line 33 "include/linux/marker.h"
typedef void marker_probe_func(void * , void * , char const   * , va_list * );
#line 34 "include/linux/marker.h"
struct marker_probe_closure {
   marker_probe_func *func ;
   void *probe_private ;
};
#line 40 "include/linux/marker.h"
struct marker {
   char const   *name ;
   char const   *format ;
   char state ;
   char ptype ;
   void (*call)(struct marker  const  * , void *  , ...) ;
   struct marker_probe_closure single ;
   struct marker_probe_closure *multi ;
   char const   *tp_name ;
   void *tp_cb ;
};
#line 273 "include/linux/rcupdate.h"
struct tracepoint;
#line 274 "include/linux/rcupdate.h"
struct tracepoint {
   char const   *name ;
   int state ;
   void **funcs ;
};
#line 155 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/local.h"
struct mod_arch_specific {

};
#line 158 "/work/ldvuser/novikov/inst/current/envs/linux/linux/arch/x86/include/asm/local.h"
struct kernel_symbol {
   unsigned long value ;
   char const   *name ;
};
#line 45 "include/linux/module.h"
struct module_attribute {
   struct attribute attr ;
   ssize_t (*show)(struct module_attribute * , struct module * , char * ) ;
   ssize_t (*store)(struct module_attribute * , struct module * , char const   * ,
                    size_t  ) ;
   void (*setup)(struct module * , char const   * ) ;
   int (*test)(struct module * ) ;
   void (*free)(struct module * ) ;
};
#line 57
struct module_param_attrs;
#line 57 "include/linux/module.h"
struct module_kobject {
   struct kobject kobj ;
   struct module *mod ;
   struct kobject *drivers_dir ;
   struct module_param_attrs *mp ;
};
#line 69
struct exception_table_entry;
#line 174
enum module_state {
    MODULE_STATE_LIVE = 0,
    MODULE_STATE_COMING = 1,
    MODULE_STATE_GOING = 2
} ;
#line 180
struct module_sect_attrs;
#line 180
struct module_notes_attrs;
#line 180 "include/linux/module.h"
struct module {
   enum module_state state ;
   struct list_head list ;
   char name[56U] ;
   struct module_kobject mkobj ;
   struct module_attribute *modinfo_attrs ;
   char const   *version ;
   char const   *srcversion ;
   struct kobject *holders_dir ;
   struct kernel_symbol  const  *syms ;
   unsigned long const   *crcs ;
   unsigned int num_syms ;
   unsigned int num_gpl_syms ;
   struct kernel_symbol  const  *gpl_syms ;
   unsigned long const   *gpl_crcs ;
   struct kernel_symbol  const  *unused_syms ;
   unsigned long const   *unused_crcs ;
   unsigned int num_unused_syms ;
   unsigned int num_unused_gpl_syms ;
   struct kernel_symbol  const  *unused_gpl_syms ;
   unsigned long const   *unused_gpl_crcs ;
   struct kernel_symbol  const  *gpl_future_syms ;
   unsigned long const   *gpl_future_crcs ;
   unsigned int num_gpl_future_syms ;
   unsigned int num_exentries ;
   struct exception_table_entry *extable ;
   int (*init)(void) ;
   void *module_init ;
   void *module_core ;
   unsigned int init_size ;
   unsigned int core_size ;
   unsigned int init_text_size ;
   unsigned int core_text_size ;
   struct mod_arch_specific arch ;
   unsigned int taints ;
   unsigned int num_bugs ;
   struct list_head bug_list ;
   struct bug_entry *bug_table ;
   Elf64_Sym *symtab ;
   unsigned int num_symtab ;
   char *strtab ;
   struct module_sect_attrs *sect_attrs ;
   struct module_notes_attrs *notes_attrs ;
   void *percpu ;
   char *args ;
   struct marker *markers ;
   unsigned int num_markers ;
   struct tracepoint *tracepoints ;
   unsigned int num_tracepoints ;
   struct list_head modules_which_use_me ;
   struct task_struct *waiter ;
   void (*exit)(void) ;
   char *refptr ;
};
#line 21 "include/linux/uio.h"
struct kvec {
   void *iov_base ;
   size_t iov_len ;
};
#line 70 "include/mtd/mtd-abi.h"
struct otp_info {
   uint32_t start ;
   uint32_t length ;
   uint32_t locked ;
};
#line 107 "include/mtd/mtd-abi.h"
struct nand_oobfree {
   uint32_t offset ;
   uint32_t length ;
};
#line 112 "include/mtd/mtd-abi.h"
struct nand_ecclayout {
   uint32_t eccbytes ;
   uint32_t eccpos[64U] ;
   uint32_t oobavail ;
   struct nand_oobfree oobfree[8U] ;
};
#line 124 "include/mtd/mtd-abi.h"
struct mtd_ecc_stats {
   uint32_t corrected ;
   uint32_t failed ;
   uint32_t badblocks ;
   uint32_t bbtblocks ;
};
#line 146
struct mtd_info;
#line 146 "include/mtd/mtd-abi.h"
struct erase_info {
   struct mtd_info *mtd ;
   uint64_t addr ;
   uint64_t len ;
   uint64_t fail_addr ;
   u_long time ;
   u_long retries ;
   unsigned int dev ;
   unsigned int cell ;
   void (*callback)(struct erase_info * ) ;
   u_long priv ;
   u_char state ;
   struct erase_info *next ;
};
#line 49 "include/linux/mtd/mtd.h"
struct mtd_erase_region_info {
   uint64_t offset ;
   uint32_t erasesize ;
   uint32_t numblocks ;
   unsigned long *lockmap ;
};
#line 56
enum ldv_11845 {
    MTD_OOB_PLACE = 0,
    MTD_OOB_AUTO = 1,
    MTD_OOB_RAW = 2
} ;
#line 71 "include/linux/mtd/mtd.h"
typedef enum ldv_11845 mtd_oob_mode_t;
#line 72 "include/linux/mtd/mtd.h"
struct mtd_oob_ops {
   mtd_oob_mode_t mode ;
   size_t len ;
   size_t retlen ;
   size_t ooblen ;
   size_t oobretlen ;
   uint32_t ooboffs ;
   uint8_t *datbuf ;
   uint8_t *oobbuf ;
};
#line 102 "include/linux/mtd/mtd.h"
struct mtd_info {
   u_char type ;
   uint32_t flags ;
   uint64_t size ;
   uint32_t erasesize ;
   uint32_t writesize ;
   uint32_t oobsize ;
   uint32_t oobavail ;
   unsigned int erasesize_shift ;
   unsigned int writesize_shift ;
   unsigned int erasesize_mask ;
   unsigned int writesize_mask ;
   char const   *name ;
   int index ;
   struct nand_ecclayout *ecclayout ;
   int numeraseregions ;
   struct mtd_erase_region_info *eraseregions ;
   int (*erase)(struct mtd_info * , struct erase_info * ) ;
   int (*point)(struct mtd_info * , loff_t  , size_t  , size_t * , void ** , resource_size_t * ) ;
   void (*unpoint)(struct mtd_info * , loff_t  , size_t  ) ;
   int (*read)(struct mtd_info * , loff_t  , size_t  , size_t * , u_char * ) ;
   int (*write)(struct mtd_info * , loff_t  , size_t  , size_t * , u_char const   * ) ;
   int (*panic_write)(struct mtd_info * , loff_t  , size_t  , size_t * , u_char const   * ) ;
   int (*read_oob)(struct mtd_info * , loff_t  , struct mtd_oob_ops * ) ;
   int (*write_oob)(struct mtd_info * , loff_t  , struct mtd_oob_ops * ) ;
   int (*get_fact_prot_info)(struct mtd_info * , struct otp_info * , size_t  ) ;
   int (*read_fact_prot_reg)(struct mtd_info * , loff_t  , size_t  , size_t * , u_char * ) ;
   int (*get_user_prot_info)(struct mtd_info * , struct otp_info * , size_t  ) ;
   int (*read_user_prot_reg)(struct mtd_info * , loff_t  , size_t  , size_t * , u_char * ) ;
   int (*write_user_prot_reg)(struct mtd_info * , loff_t  , size_t  , size_t * , u_char * ) ;
   int (*lock_user_prot_reg)(struct mtd_info * , loff_t  , size_t  ) ;
   int (*writev)(struct mtd_info * , struct kvec  const  * , unsigned long  , loff_t  ,
                 size_t * ) ;
   void (*sync)(struct mtd_info * ) ;
   int (*lock)(struct mtd_info * , loff_t  , uint64_t  ) ;
   int (*unlock)(struct mtd_info * , loff_t  , uint64_t  ) ;
   int (*suspend)(struct mtd_info * ) ;
   void (*resume)(struct mtd_info * ) ;
   int (*block_isbad)(struct mtd_info * , loff_t  ) ;
   int (*block_markbad)(struct mtd_info * , loff_t  ) ;
   struct notifier_block reboot_notifier ;
   struct mtd_ecc_stats ecc_stats ;
   int subpage_sft ;
   void *priv ;
   struct module *owner ;
   int usecount ;
   int (*get_device)(struct mtd_info * ) ;
   void (*put_device)(struct mtd_info * ) ;
};
#line 295 "include/linux/mtd/mtd.h"
struct mtd_partition {
   char *name ;
   uint64_t size ;
   uint64_t offset ;
   uint32_t mask_flags ;
   struct nand_ecclayout *ecclayout ;
   struct mtd_info **mtdp ;
};
#line 53 "include/linux/mtd/partitions.h"
struct mtd_part_parser {
   struct list_head list ;
   struct module *owner ;
   char const   *name ;
   int (*parse_fn)(struct mtd_info * , struct mtd_partition ** , unsigned long  ) ;
};
#line 156 "include/linux/bootmem.h"
struct ar7_bin_rec {
   unsigned int checksum ;
   unsigned int length ;
   unsigned int address ;
};
#line 347 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
typedef int ldv_func_ret_type___1;
#line 238 "include/linux/kernel.h"
extern int printk(char const   *  , ...) ;
#line 43 "include/linux/string.h"
extern int strncmp(char const   * , char const   * , __kernel_size_t  ) ;
#line 5 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
extern void __ldv_spin_lock(spinlock_t * ) ;
#line 8
void ldv___ldv_spin_lock_1(spinlock_t *ldv_func_arg1 ) ;
#line 12
void ldv___ldv_spin_lock_4(spinlock_t *ldv_func_arg1 ) ;
#line 14
extern void __ldv_spin_unlock(spinlock_t * ) ;
#line 17
void ldv___ldv_spin_unlock_2(spinlock_t *ldv_func_arg1 ) ;
#line 21
void ldv___ldv_spin_unlock_5(spinlock_t *ldv_func_arg1 ) ;
#line 23
extern int __ldv_spin_trylock(spinlock_t * ) ;
#line 26
int ldv___ldv_spin_trylock_3(spinlock_t *ldv_func_arg1 ) ;
#line 32
void ldv_spin_lock_dma_spin_lock(void) ;
#line 33
void ldv_spin_unlock_dma_spin_lock(void) ;
#line 40
void ldv_spin_lock_lock_of_NOT_ARG_SIGN(void) ;
#line 41
void ldv_spin_unlock_lock_of_NOT_ARG_SIGN(void) ;
#line 42
int ldv_spin_trylock_lock_of_NOT_ARG_SIGN(void) ;
#line 205 "include/linux/slub_def.h"
extern void *__kmalloc(size_t  , gfp_t  ) ;
#line 212 "include/linux/slub_def.h"
__inline static void *kmalloc(size_t size , gfp_t flags ) 
{ 
  void *tmp___2 ;

  {
#line 227
  tmp___2 = __kmalloc(size, flags);
#line 227
  return (tmp___2);
}
}
#line 304 "include/linux/slab.h"
__inline static void *kzalloc(size_t size , gfp_t flags ) 
{ 
  void *tmp ;

  {
#line 306
  tmp = kmalloc(size, flags | 32768U);
#line 306
  return (tmp);
}
}
#line 86 "include/linux/module.h"
extern struct module __this_module ;
#line 65 "include/linux/mtd/partitions.h"
extern int register_mtd_parser(struct mtd_part_parser * ) ;
#line 75 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
static int create_mtd_partitions(struct mtd_info *master , struct mtd_partition **pparts ,
                                 unsigned long origin ) 
{ 
  struct ar7_bin_rec header ;
  unsigned int offset ;
  size_t len ;
  unsigned int pre_size ;
  unsigned int post_size ;
  unsigned int root_offset ;
  int retries ;
  struct mtd_partition *ar7_parts ;
  void *tmp ;
  int tmp___0 ;
  int tmp___1 ;

  {
#line 82
  pre_size = master->erasesize;
#line 82
  post_size = 0U;
#line 83
  root_offset = 917504U;
#line 85
  retries = 10;
#line 88
  tmp = kzalloc(192UL, 208U);
#line 88
  ar7_parts = (struct mtd_partition *)tmp;
#line 89
  if ((unsigned long )ar7_parts == (unsigned long )((struct mtd_partition *)0)) {
#line 90
    return (-12);
  } else {

  }
#line 91
  ar7_parts->name = (char *)"loader";
#line 92
  ar7_parts->offset = 0ULL;
#line 93
  ar7_parts->size = (uint64_t )master->erasesize;
#line 94
  ar7_parts->mask_flags = 1024U;
#line 96
  (ar7_parts + 1UL)->name = (char *)"config";
#line 97
  (ar7_parts + 1UL)->offset = 0ULL;
#line 98
  (ar7_parts + 1UL)->size = (uint64_t )master->erasesize;
#line 99
  (ar7_parts + 1UL)->mask_flags = 0U;
  ldv_10762: 
#line 102
  offset = pre_size;
#line 103
  (*(master->read))(master, (loff_t )offset, 12UL, & len, (u_char *)(& header));
#line 105
  tmp___0 = strncmp((char const   *)(& header), "TIENV0.8", 8UL);
#line 105
  if (tmp___0 == 0) {
#line 106
    (ar7_parts + 1UL)->offset = (uint64_t )pre_size;
  } else {

  }
#line 107
  if (header.checksum == 4277008962U) {
#line 108
    goto ldv_10761;
  } else {

  }
#line 109
  if (header.checksum == 4276949633U) {
#line 110
    goto ldv_10761;
  } else {

  }
#line 111
  pre_size = master->erasesize + pre_size;
#line 112
  tmp___1 = retries;
#line 112
  retries = retries - 1;
#line 112
  if (tmp___1 != 0) {
#line 113
    goto ldv_10762;
  } else {

  }
  ldv_10761: 
#line 114
  pre_size = offset;
#line 116
  if ((ar7_parts + 1UL)->offset == 0ULL) {
#line 117
    (ar7_parts + 1UL)->offset = master->size - (uint64_t )master->erasesize;
#line 118
    post_size = master->erasesize;
  } else {

  }
#line 121
  switch (header.checksum) {
  case 4277008962U: ;
#line 123
  goto ldv_10765;
  ldv_10764: 
#line 124
  offset = (header.length + offset) + 12U;
#line 125
  (*(master->read))(master, (loff_t )offset, 12UL, & len, (u_char *)(& header));
  ldv_10765: ;
#line 123
  if (header.length != 0U) {
#line 124
    goto ldv_10764;
  } else {

  }
#line 128
  root_offset = offset + 16U;
#line 129
  goto ldv_10767;
  case 4276949633U: ;
#line 131
  goto ldv_10770;
  ldv_10769: 
#line 132
  offset = (header.length + offset) + 12U;
#line 133
  (*(master->read))(master, (loff_t )offset, 12UL, & len, (u_char *)(& header));
  ldv_10770: ;
#line 131
  if (header.length != 0U) {
#line 132
    goto ldv_10769;
  } else {

  }
#line 136
  root_offset = offset + 271U;
#line 137
  root_offset = root_offset & 4294967040U;
#line 138
  goto ldv_10767;
  default: 
#line 140
  printk("<4>Unknown magic: %08x\n", header.checksum);
#line 141
  goto ldv_10767;
  }
  ldv_10767: 
#line 144
  (*(master->read))(master, (loff_t )root_offset, 12UL, & len, (u_char *)(& header));
#line 146
  if (header.checksum != 1936814952U) {
#line 147
    root_offset = (master->erasesize + root_offset) - 1U;
#line 148
    root_offset = - master->erasesize & root_offset;
  } else {

  }
#line 151
  (ar7_parts + 2UL)->name = (char *)"linux";
#line 152
  (ar7_parts + 2UL)->offset = (uint64_t )pre_size;
#line 153
  (ar7_parts + 2UL)->size = (master->size - (uint64_t )pre_size) - (uint64_t )post_size;
#line 154
  (ar7_parts + 2UL)->mask_flags = 0U;
#line 156
  (ar7_parts + 3UL)->name = (char *)"rootfs";
#line 157
  (ar7_parts + 3UL)->offset = (uint64_t )root_offset;
#line 158
  (ar7_parts + 3UL)->size = (master->size - (uint64_t )root_offset) - (uint64_t )post_size;
#line 159
  (ar7_parts + 3UL)->mask_flags = 0U;
#line 161
  *pparts = ar7_parts;
#line 162
  return (4);
}
}
#line 165 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
static struct mtd_part_parser ar7_parser  =    {{0, 0}, & __this_module, "ar7part", & create_mtd_partitions};
#line 171 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
static int ar7_parser_init(void) 
{ 
  int tmp ;

  {
#line 173
  tmp = register_mtd_parser(& ar7_parser);
#line 173
  return (tmp);
}
}
#line 199
void ldv_check_final_state(void) ;
#line 208
void ldv_initialize(void) ;
#line 211
extern void ldv_handler_precall(void) ;
#line 214
extern int nondet_int(void) ;
#line 217 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
int LDV_IN_INTERRUPT  ;
#line 220 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
void ldv_main0_sequence_infinite_withcheck_stateful(void) 
{ 
  struct mtd_info *var_group1 ;
  struct mtd_partition **var_group2 ;
  unsigned long var_create_mtd_partitions_0_p2 ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;

  {
#line 250
  LDV_IN_INTERRUPT = 1;
#line 259
  ldv_initialize();
#line 273
  ldv_handler_precall();
#line 274
  tmp = ar7_parser_init();
#line 274
  if (tmp != 0) {
#line 275
    goto ldv_final;
  } else {

  }
#line 279
  goto ldv_10809;
  ldv_10808: 
#line 282
  tmp___0 = nondet_int();
#line 282
  switch (tmp___0) {
  case 0: 
#line 300
  ldv_handler_precall();
#line 301
  create_mtd_partitions(var_group1, var_group2, var_create_mtd_partitions_0_p2);
#line 308
  goto ldv_10806;
  default: ;
#line 309
  goto ldv_10806;
  }
  ldv_10806: ;
  ldv_10809: 
#line 279
  tmp___1 = nondet_int();
#line 279
  if (tmp___1 != 0) {
#line 280
    goto ldv_10808;
  } else {

  }


  ldv_final: 
#line 318
  ldv_check_final_state();
#line 321
  return;
}
}
#line 325 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
void ldv___ldv_spin_lock_1(spinlock_t *ldv_func_arg1 ) 
{ 


  {
#line 330
  ldv_spin_lock_lock_of_NOT_ARG_SIGN();
#line 332
  __ldv_spin_lock(ldv_func_arg1);
#line 333
  return;
}
}
#line 335 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
void ldv___ldv_spin_unlock_2(spinlock_t *ldv_func_arg1 ) 
{ 


  {
#line 340
  ldv_spin_unlock_lock_of_NOT_ARG_SIGN();
#line 342
  __ldv_spin_unlock(ldv_func_arg1);
#line 343
  return;
}
}
#line 345 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
int ldv___ldv_spin_trylock_3(spinlock_t *ldv_func_arg1 ) 
{ 
  ldv_func_ret_type___1 ldv_func_res ;
  int tmp ;
  int tmp___0 ;

  {
#line 350
  tmp = __ldv_spin_trylock(ldv_func_arg1);
#line 350
  ldv_func_res = tmp;
#line 352
  tmp___0 = ldv_spin_trylock_lock_of_NOT_ARG_SIGN();
#line 352
  return (tmp___0);
#line 354
  return (ldv_func_res);
}
}
#line 357 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
void ldv___ldv_spin_lock_4(spinlock_t *ldv_func_arg1 ) 
{ 


  {
#line 362
  ldv_spin_lock_dma_spin_lock();
#line 364
  __ldv_spin_lock(ldv_func_arg1);
#line 365
  return;
}
}
#line 367 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/dscv/ri/39_7a/drivers/mtd/ar7part.c.prepared"
void ldv___ldv_spin_unlock_5(spinlock_t *ldv_func_arg1 ) 
{ 


  {
#line 372
  ldv_spin_unlock_dma_spin_lock();
#line 374
  __ldv_spin_unlock(ldv_func_arg1);
#line 375
  return;
}
}
#line 1 "<compiler builtins>"
long __builtin_expect(long exp , long c ) ;
#line 10 "/home/ldvuser/ldv/inst/kernel-rules/verifier/rcv.h"
__inline static void ldv_error(void) 
{ 


  {
  LDV_ERROR: 
#line 12
  goto LDV_ERROR;
}
}
#line 25
extern int ldv_undef_int(void) ;
#line 49 "/home/ldvuser/ldv/inst/kernel-rules/verifier/rcv.h"
long __builtin_expect(long exp , long c ) 
{ 


  {
#line 51
  return (exp);
}
}
#line 8 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
static int ldv_spin_dma_spin_lock  ;
#line 11 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_spin_lock_dma_spin_lock(void) 
{ 


  {
#line 14
  if (ldv_spin_dma_spin_lock == 1) {

  } else {
#line 14
    ldv_error();
  }
#line 16
  ldv_spin_dma_spin_lock = 2;
#line 17
  return;
}
}
#line 20 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_spin_unlock_dma_spin_lock(void) 
{ 


  {
#line 23
  if (ldv_spin_dma_spin_lock == 2) {

  } else {
#line 23
    ldv_error();
  }
#line 25
  ldv_spin_dma_spin_lock = 1;
#line 26
  return;
}
}
#line 29 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_trylock_dma_spin_lock(void) 
{ 
  int is_spin_held_by_another_thread ;

  {
#line 34
  if (ldv_spin_dma_spin_lock == 1) {

  } else {
#line 34
    ldv_error();
  }
#line 37
  is_spin_held_by_another_thread = ldv_undef_int();
#line 40
  if (is_spin_held_by_another_thread) {
#line 43
    return (0);
  } else {
#line 48
    ldv_spin_dma_spin_lock = 2;
#line 50
    return (1);
  }
}
}
#line 55 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_spin_unlock_wait_dma_spin_lock(void) 
{ 


  {
#line 58
  if (ldv_spin_dma_spin_lock == 1) {

  } else {
#line 58
    ldv_error();
  }
#line 59
  return;
}
}
#line 62 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_is_locked_dma_spin_lock(void) 
{ 
  int is_spin_held_by_another_thread ;

  {
#line 67
  is_spin_held_by_another_thread = ldv_undef_int();
#line 70
  if (ldv_spin_dma_spin_lock == 1 && ! is_spin_held_by_another_thread) {
#line 73
    return (0);
  } else {
#line 78
    return (1);
  }
}
}
#line 83 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_can_lock_dma_spin_lock(void) 
{ 
  int tmp ;
  int tmp___0 ;

  {
#line 86
  tmp = ldv_spin_is_locked_dma_spin_lock();
#line 86
  if (tmp) {
#line 86
    tmp___0 = 0;
  } else {
#line 86
    tmp___0 = 1;
  }
#line 86
  return (tmp___0);
}
}
#line 90 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_is_contended_dma_spin_lock(void) 
{ 
  int is_spin_contended ;

  {
#line 95
  is_spin_contended = ldv_undef_int();
#line 98
  if (is_spin_contended) {
#line 101
    return (0);
  } else {
#line 106
    return (1);
  }
}
}
#line 111 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_atomic_dec_and_lock_dma_spin_lock(void) 
{ 
  int atomic_value_after_dec ;

  {
#line 116
  if (ldv_spin_dma_spin_lock == 1) {

  } else {
#line 116
    ldv_error();
  }
#line 119
  atomic_value_after_dec = ldv_undef_int();
#line 122
  if (atomic_value_after_dec == 0) {
#line 125
    ldv_spin_dma_spin_lock = 2;
#line 127
    return (1);
  } else {

  }
#line 131
  return (0);
}
}
#line 133 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
static int ldv_spin_lock_of_NOT_ARG_SIGN  ;
#line 136 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_spin_lock_lock_of_NOT_ARG_SIGN(void) 
{ 


  {
#line 139
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 1) {

  } else {
#line 139
    ldv_error();
  }
#line 141
  ldv_spin_lock_of_NOT_ARG_SIGN = 2;
#line 142
  return;
}
}
#line 145 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_spin_unlock_lock_of_NOT_ARG_SIGN(void) 
{ 


  {
#line 148
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 2) {

  } else {
#line 148
    ldv_error();
  }
#line 150
  ldv_spin_lock_of_NOT_ARG_SIGN = 1;
#line 151
  return;
}
}
#line 154 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_trylock_lock_of_NOT_ARG_SIGN(void) 
{ 
  int is_spin_held_by_another_thread ;

  {
#line 159
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 1) {

  } else {
#line 159
    ldv_error();
  }
#line 162
  is_spin_held_by_another_thread = ldv_undef_int();
#line 165
  if (is_spin_held_by_another_thread) {
#line 168
    return (0);
  } else {
#line 173
    ldv_spin_lock_of_NOT_ARG_SIGN = 2;
#line 175
    return (1);
  }
}
}
#line 180 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_spin_unlock_wait_lock_of_NOT_ARG_SIGN(void) 
{ 


  {
#line 183
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 1) {

  } else {
#line 183
    ldv_error();
  }
#line 184
  return;
}
}
#line 187 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_is_locked_lock_of_NOT_ARG_SIGN(void) 
{ 
  int is_spin_held_by_another_thread ;

  {
#line 192
  is_spin_held_by_another_thread = ldv_undef_int();
#line 195
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 1 && ! is_spin_held_by_another_thread) {
#line 198
    return (0);
  } else {
#line 203
    return (1);
  }
}
}
#line 208 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_can_lock_lock_of_NOT_ARG_SIGN(void) 
{ 
  int tmp ;
  int tmp___0 ;

  {
#line 211
  tmp = ldv_spin_is_locked_lock_of_NOT_ARG_SIGN();
#line 211
  if (tmp) {
#line 211
    tmp___0 = 0;
  } else {
#line 211
    tmp___0 = 1;
  }
#line 211
  return (tmp___0);
}
}
#line 215 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_spin_is_contended_lock_of_NOT_ARG_SIGN(void) 
{ 
  int is_spin_contended ;

  {
#line 220
  is_spin_contended = ldv_undef_int();
#line 223
  if (is_spin_contended) {
#line 226
    return (0);
  } else {
#line 231
    return (1);
  }
}
}
#line 236 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
int ldv_atomic_dec_and_lock_lock_of_NOT_ARG_SIGN(void) 
{ 
  int atomic_value_after_dec ;

  {
#line 241
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 1) {

  } else {
#line 241
    ldv_error();
  }
#line 244
  atomic_value_after_dec = ldv_undef_int();
#line 247
  if (atomic_value_after_dec == 0) {
#line 250
    ldv_spin_lock_of_NOT_ARG_SIGN = 2;
#line 252
    return (1);
  } else {

  }
#line 256
  return (0);
}
}
#line 260 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_initialize(void) 
{ 


  {
#line 263
  ldv_spin_dma_spin_lock = 1;
#line 265
  ldv_spin_lock_of_NOT_ARG_SIGN = 1;
#line 266
  return;
}
}
#line 269 "/work/ldvuser/novikov/work/current--X--drivers/mtd/ar7part.ko--X--defaultlinux--X--39_7a--X--cpachecker/linux/csd_deg_dscv/11/dscv_tempdir/rule-instrumentor/39_7a/common-model/ldv_common_model.c"
void ldv_check_final_state(void) 
{ 


  {
#line 272
  if (ldv_spin_dma_spin_lock == 1) {

  } else {
#line 272
    ldv_error();
  }
#line 274
  if (ldv_spin_lock_of_NOT_ARG_SIGN == 1) {

  } else {
#line 274
    ldv_error();
  }
#line 275
  return;
}
}
