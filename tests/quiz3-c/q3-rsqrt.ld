ENTRY(_start)
SECTIONS {
  . = 0x00000000;
  .text   : { *(.text*) }
  .rodata : { *(.rodata*) }
  .data   : { *(.data*) }
  .bss (NOLOAD) : { *(.bss*) *(COMMON) }
}

