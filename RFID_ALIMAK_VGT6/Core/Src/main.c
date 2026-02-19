/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : EM4095/EM4100 edge->Manchester (PA0 EXTI + TIM2 ~1us)
  ******************************************************************************
  */
/* USER CODE END Header */

#include "main.h"
#include "gpio.h"
#include "usart.h"
#include "tim.h"


#include <stdint.h>

#include <string.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>   /* qsort */

/* prueba commit */
/* prueba commit */
/* prueba commit */
/* prueba commit new brach write */
/* prueba commit GitLab */
/* prueba commit GitLab */
/* prueba commit GitLab */

/* ===================== CONFIG ===================== */
#define DT_BUF_SZ        4096
#define HL_BUF_SZ        8192
#define BIT_BUF_SZ       2048   /* un poco más para tener margen */


/* fin de frame si dt > GAP_US (si hay “hueco” real) */
#define GAP_US           5500u

/* además, fin de frame por ventana aunque no haya GAP */
#define WIN_MS           80u       /* 50..80 ms suele ir bien para EM4100 (~32ms/frame) */
#define WIN_EDGES        1000u     /* corte duro por edges para no desbordar */

#define MIN_EDGES        150u      /* mejor un poco más alto que 80 */
#define MAX_EDGES        (DT_BUF_SZ)

#define DT_MIN_US        50u
#define DT_MAX_US        2000u

#define HALF_MIN_US      140u
#define HALF_MAX_US      400u

/* tolerancia para cuantizar dt a múltiplos de half-periods */
#define Q_TOL_PCT        95

/* estabilidad: cuántas lecturas iguales seguidas para “aceptar” ID */
#define STABLE_HITS      3

/* rate limit del NO ID (ms) */
#define NOID_PRINT_EVERY_MS  500u

/* ===================== UART PRINT ===================== */
static void uart_printf(const char *fmt, ...)
{
  char buf[256];
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(buf, sizeof(buf), fmt, ap);
  va_end(ap);

  if (n > 0)
  {
    if (n > (int)sizeof(buf)) n = (int)sizeof(buf);
    HAL_UART_Transmit(&huart2, (uint8_t*)buf, (uint16_t)n, HAL_MAX_DELAY);
  }
}

/* ===================== CAPTURE BUFFERS (ISR) ===================== */
static volatile uint32_t dt_buf[DT_BUF_SZ];
static volatile uint8_t  lv_buf[DT_BUF_SZ];   /* nivel DURANTE el dt (nivel previo al flanco) */
static volatile uint16_t dt_n = 0;

static volatile uint8_t  have_last = 0;
static volatile uint32_t last_cnt = 0;
static volatile uint8_t  last_lv = 0;

static volatile uint8_t  frame_ready = 0;
static volatile uint16_t frame_n = 0;

/* control de ventana */
static volatile uint8_t  cap_active = 0;
static volatile uint32_t cap_start_ms = 0;

/* ===================== LOCAL WORK BUFFERS (MAIN) ===================== */
static uint32_t dt_local[DT_BUF_SZ];
static uint8_t  lv_local[DT_BUF_SZ];

static uint8_t  hl_buf[HL_BUF_SZ];
static uint16_t hl_n;

static uint8_t  bits[BIT_BUF_SZ];
static uint16_t bits_n;

/* ===================== UTILS ===================== */
static int u32_cmp(const void *a, const void *b)
{
  uint32_t ua = *(const uint32_t*)a;
  uint32_t ub = *(const uint32_t*)b;
  if (ua < ub) return -1;
  if (ua > ub) return  1;
  return 0;
}

static uint32_t median_u32(uint32_t *v, uint16_t n)
{
  qsort(v, n, sizeof(uint32_t), u32_cmp);
  return v[n/2];
}

static bool within_pct(uint32_t val, uint32_t ref, uint32_t pct)
{
  uint32_t diff = (val > ref) ? (val - ref) : (ref - val);
  return (diff * 100u) <= (ref * pct);
}

static uint32_t estimate_half_us(const uint32_t *dt, uint16_t n)
{
  /* coger dt “cortos” típicos ~250us */
  uint32_t tmp[512];
  uint16_t m = 0;

  for (uint16_t i = 0; i < n && m < 512; i++)
  {
    uint32_t d = dt[i];
    if (d >= HALF_MIN_US && d <= HALF_MAX_US)
      tmp[m++] = d;
  }
  if (m < 12) return 0;
  return median_u32(tmp, m);
}

/* ===================== EDGE dt -> HALFLEVELS ===================== */
static int dt_to_halflevels(const uint32_t *dt, const uint8_t *lv, uint16_t n,
                            uint32_t half_us,
                            uint8_t *hl, uint16_t *out_hl_n)
{
  uint16_t k = 0;
  if (half_us == 0) return -1;

  for (uint16_t i = 0; i < n; i++)
  {
    uint32_t d = dt[i];
    if (d < DT_MIN_US || d > DT_MAX_US)
      continue;

    /* cuantiza a múltiplos de half_us: 1..8 */
    uint32_t q = (d + (half_us/2u)) / half_us;
    if (q < 1) q = 1;
    if (q > 8) q = 8;

    uint32_t target = q * half_us;
    if (!within_pct(d, target, Q_TOL_PCT))
      continue;

    for (uint32_t j = 0; j < q; j++)
    {
      if (k >= HL_BUF_SZ) return -2;
      hl[k++] = lv[i] ? 1 : 0;
    }
  }

  *out_hl_n = k;
  return (k >= 80) ? 0 : -3; /* pide un poco más de “chicha” */
}

/* ===================== HALFLEVELS -> MANCHESTER BITS ===================== */
/* polarity:
   0: 01 -> bit=1, 10 -> bit=0
   1: 01 -> bit=0, 10 -> bit=1
*/
static int manchester_from_halflevels(const uint8_t *hl, uint16_t n_hl,
                                      uint8_t polarity,
                                      uint8_t *out_bits, uint16_t *out_nbits)
{
  uint16_t nb = 0;
  uint16_t i = 0;

  while ((i + 1) < n_hl)
  {
    uint8_t a = hl[i];
    uint8_t b = hl[i + 1];

    if (a == b)
      return -21; /* Manchester inválido */

    uint8_t bit;
    if (polarity == 0)
      bit = (a == 0 && b == 1) ? 1 : 0;  /* 01->1, 10->0 */
    else
      bit = (a == 0 && b == 1) ? 0 : 1;  /* invert */

    if (nb >= BIT_BUF_SZ) return -22;
    out_bits[nb++] = bit;

    i += 2;
  }

  *out_nbits = nb;
  return (nb >= 64) ? 0 : -23;
}

/* ===================== EM4100 decode con paridad ===================== */
/*
  Formato típico EM4100 (wire data):
   - Header: 9 x '1'
   - Start bit: '0'
   - 10 grupos: [D3 D2 D1 D0 Prow]  (Prow = paridad EVEN de los 4 data)
   - 4 bits de paridad de columna: Pc3 Pc2 Pc1 Pc0 (EVEN con las 10 filas)
   - Stop bit: '0'
  Total: 9 + 1 + 50 + 4 + 1 = 65 bits

  Nota: algunos decoders se saltan “start” o lo cuentan distinto.
  Aquí probamos offsets robustos: con start y sin start.
*/

static int parity_even_5(const uint8_t *p4, uint8_t prow)
{
  /* even parity: (sum(data)+prow) %2 == 0 */
  uint8_t s = (p4[0] + p4[1] + p4[2] + p4[3] + (prow & 1)) & 1;
  return (s == 0) ? 0 : -1;
}

static int decode_em4100_at(const uint8_t *b, uint16_t nb, uint16_t data_start, char id40[11])
{
  /* necesitamos 10*5 + 4 + 1 = 55 bits desde data_start */
  if (data_start + 55 > nb) return -10;

  uint8_t row[10][4];
  uint8_t prow[10];

  /* leer 10 filas */
  for (uint8_t r = 0; r < 10; r++)
  {
    uint16_t base = data_start + r * 5;
    row[r][0] = b[base + 0] & 1; /* D3 */
    row[r][1] = b[base + 1] & 1; /* D2 */
    row[r][2] = b[base + 2] & 1; /* D1 */
    row[r][3] = b[base + 3] & 1; /* D0 */
    prow[r]   = b[base + 4] & 1;

    if (parity_even_5(row[r], prow[r]) != 0)
      return -11;
  }

  /* paridad de columnas */
  uint16_t pc_base = data_start + 10 * 5;
  uint8_t pc[4] = { b[pc_base+0]&1, b[pc_base+1]&1, b[pc_base+2]&1, b[pc_base+3]&1 };

  for (uint8_t c = 0; c < 4; c++)
  {
    uint8_t sum = pc[c];
    for (uint8_t r = 0; r < 10; r++)
      sum ^= row[r][c]; /* XOR = parity mod2 */
    /* even parity => XOR total debe ser 0 */
    if (sum != 0) return -12;
  }

  /* stop bit */
  uint8_t stop = b[pc_base + 4] & 1;
  if (stop != 0) return -13;

  /* formar nibbles (10) y volcar a hex */
  static const char hex[] = "0123456789ABCDEF";
  for (uint8_t r = 0; r < 10; r++)
  {
    uint8_t v = (row[r][0]<<3) | (row[r][1]<<2) | (row[r][2]<<1) | (row[r][3]<<0);
    id40[r] = hex[v & 0xF];
  }
  id40[10] = '\0';
  return 0;
}

static int find_and_decode_em4100(const uint8_t *b, uint16_t nb, uint16_t *pre_idx,
                                  char id40[11], uint8_t *used_start0)
{
  /* busca 9 unos seguidos */
  for (uint16_t i = 0; i + 9 < nb; i++)
  {
    bool ok = true;
    for (uint8_t k = 0; k < 9; k++)
    {
      if (b[i + k] != 1) { ok = false; break; }
    }
    if (!ok) continue;

    /* opción A: hay start bit 0 justo después */
    uint16_t dsA = i + 9;
    if (dsA < nb && b[dsA] == 0)
    {
      uint16_t dataA = dsA + 1; /* after start 0 */
      if (decode_em4100_at(b, nb, dataA, id40) == 0)
      {
        *pre_idx = i;
        *used_start0 = 1;
        return 0;
      }
    }

    /* opción B: sin start explícito (data empieza justo después de 9 unos) */
    uint16_t dataB = i + 9;
    if (decode_em4100_at(b, nb, dataB, id40) == 0)
    {
      *pre_idx = i;
      *used_start0 = 0;
      return 0;
    }
  }
  return -20;
}

/* ===================== PROCESS ONE FRAME ===================== */
static void process_frame(const uint32_t *dt, const uint8_t *lv, uint16_t n)
{
  static uint32_t last_noid_ms = 0;

  uint32_t half = estimate_half_us(dt, n);
  if (!half)
  {
    uint32_t ms = HAL_GetTick();
    if ((ms - last_noid_ms) >= NOID_PRINT_EVERY_MS)
    {
      uart_printf("NO ID: no pude estimar T/2 (n=%u)\r\n", n);
      last_noid_ms = ms;
    }
    return;
  }

  int rc = dt_to_halflevels(dt, lv, n, half, hl_buf, &hl_n);
  if (rc != 0)
  {
    uint32_t ms = HAL_GetTick();
    if ((ms - last_noid_ms) >= NOID_PRINT_EVERY_MS)
    {
      uart_printf("NO ID: dt_to_halflevels rc=%d (T/2=%lu, n=%u)\r\n",
                  rc, (unsigned long)half, n);
      last_noid_ms = ms;
    }
    return;
  }

  /* probar combinaciones: inv (invertir niveles) y polarity */
  static uint8_t hl_inv[HL_BUF_SZ];
  for (uint16_t i = 0; i < hl_n; i++) hl_inv[i] = hl_buf[i] ^ 1;
  const uint8_t *cands_hl[2] = { hl_buf, hl_inv };

  /* estabilidad */
  static char last_id[11] = {0};
  static uint8_t stable_cnt = 0;
  static uint32_t last_ok_ms = 0;

  for (uint8_t inv = 0; inv < 2; inv++)
  {
    for (uint8_t pol = 0; pol < 2; pol++)
    {
      int drc = manchester_from_halflevels(cands_hl[inv], hl_n, pol, bits, &bits_n);
      if (drc != 0) continue;

      uint16_t pre = 0;
      uint8_t used_start0 = 0;
      char id40[11];

      if (find_and_decode_em4100(bits, bits_n, &pre, id40, &used_start0) == 0)
      {
        /* estabilidad: mismo ID repetido */
        if (strncmp(last_id, id40, 10) == 0)
        {
          if (stable_cnt < 255) stable_cnt++;
        }
        else
        {
          strncpy(last_id, id40, 11);
          stable_cnt = 1;
        }

        if (stable_cnt >= STABLE_HITS)
        {
          uint32_t ms = HAL_GetTick();
          /* opcional: si quieres que lo repita continuamente mientras esté el tag,
             quita este if y que imprima siempre */
          if (ms - last_ok_ms > 80)  /* no spamear demasiado */
          {
            uart_printf("OK: T/2~%luus edges=%u inv=%u pol=%u pre=%u start0=%u ID40=%s (stable=%u)\r\n",
                        (unsigned long)half, n, inv, pol, pre, used_start0, id40, stable_cnt);
            last_ok_ms = ms;
          }
          return;
        }

        /* si aún no es estable, no grites “NO ID” */
        return;
      }
    }
  }

  /* si no decodificó nada con paridad OK */
  uint32_t ms = HAL_GetTick();
  if ((ms - last_noid_ms) >= NOID_PRINT_EVERY_MS)
  {
    uart_printf("NO ID (T/2~%luus, edges=%u). Revisa pull/umbral/ruido.\r\n",
                (unsigned long)half, n);
    last_noid_ms = ms;
  }
}

/* ===================== EXTI CALLBACK ===================== */
void HAL_GPIO_EXTI_Callback(uint16_t GPIO_Pin)
{
  if (GPIO_Pin != GPIO_PIN_0) return; /* PA0 */

  uint32_t now = __HAL_TIM_GET_COUNTER(&htim2);
  uint8_t cur_lv = (uint8_t)HAL_GPIO_ReadPin(GPIOA, GPIO_PIN_0);
  uint32_t ms = HAL_GetTick();

  if (!have_last)
  {
    have_last = 1;
    last_cnt = now;
    last_lv  = cur_lv;
    dt_n = 0;

    cap_active = 1;
    cap_start_ms = ms;
    return;
  }

  uint32_t dt = (now >= last_cnt) ? (now - last_cnt)
                                  : (0xFFFFFFFFu - last_cnt + 1u + now);

  if (!cap_active)
  {
    cap_active = 1;
    cap_start_ms = ms;
    dt_n = 0;
  }

  if (dt_n < MAX_EDGES)
  {
    dt_buf[dt_n] = dt;
    lv_buf[dt_n] = last_lv; /* nivel antes del flanco */
    dt_n++;
  }
  else
  {
    if (!frame_ready && dt_n >= MIN_EDGES)
    {
      frame_n = dt_n;
      frame_ready = 1;
    }
    dt_n = 0;
    cap_active = 0;
  }

  /* criterios de fin de frame */
  uint8_t end = 0;
  if (dt > GAP_US) end = 1;
  if ((ms - cap_start_ms) >= WIN_MS) end = 1;
  if (dt_n >= WIN_EDGES) end = 1;

  if (end)
  {
    if (!frame_ready && dt_n >= MIN_EDGES)
    {
      frame_n = dt_n;
      frame_ready = 1;
    }
    dt_n = 0;
    cap_active = 0;
  }

  last_cnt = now;
  last_lv  = cur_lv;
}

/* ===================== CLOCK (HSI 16MHz SIMPLE) ===================== */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};

  __HAL_RCC_PWR_CLK_ENABLE();

  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSI;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.HSICalibrationValue = RCC_HSICALIBRATION_DEFAULT;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_OFF;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }

  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_SYSCLK | RCC_CLOCKTYPE_HCLK |
                                RCC_CLOCKTYPE_PCLK1  | RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_HSI;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV1;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_0) != HAL_OK)
  {
    Error_Handler();
  }
}

/* ===================== ERROR HANDLER ===================== */
void Error_Handler(void)
{
  __disable_irq();
  while (1) { }
}

/* ===================== MAIN ===================== */
int main(void)
{
  HAL_Init();
  SystemClock_Config();

  MX_GPIO_Init();
  MX_USART2_UART_Init();
  MX_TIM2_Init();

  HAL_TIM_Base_Start(&htim2);

  uart_printf("\r\n=== EM4095/EM4100 EDGE->MANCHESTER (PA0 EXTI + TIM2) ===\r\n");
  uart_printf("TIM2 tick ~1us si TIMCLK=16MHz y PSC=15\r\n");
  uart_printf("Ventana: %ums o %u edges (GAP=%uus)\r\n", WIN_MS, WIN_EDGES, GAP_US);
  uart_printf("Estabilidad: %u lecturas iguales\r\n", STABLE_HITS);
  uart_printf("Acerca el tag...\r\n");

  while (1)
  {
    if (frame_ready)
    {
      __disable_irq();
      uint16_t n = frame_n;
      if (n > DT_BUF_SZ) n = DT_BUF_SZ;
      memcpy(dt_local, (const void*)dt_buf, n * sizeof(uint32_t));
      memcpy(lv_local, (const void*)lv_buf, n * sizeof(uint8_t));
      frame_ready = 0;
      __enable_irq();

      process_frame(dt_local, lv_local, n);
    }

    HAL_Delay(2);
  }
}
