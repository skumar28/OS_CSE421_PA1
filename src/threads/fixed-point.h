/**
 * New File added for fixed point real arithmetic calculations
 */
#define FIX_F (1 << 14) /* pow(2, 14) */
#define FIX_MIN_INT -(1<<32)/FIX_F
#define FIX_MAX_INT (1<<31 -1)/FIX_F

/* Packing style: 14 LSB fractional, 16 MSB integer */
/* Efficient: recommended */
typedef struct fixed_point_t{
int v;
} fixed_point_t;

fixed_point_t fix_mul(int x, int y);
fixed_point_t fix_div(int x, int y);

fixed_point_t fix_mul(int x, int y) {

	fixed_point_t f = { (((long long) x * y) / FIX_F) };
	return f;
}

fixed_point_t fix_div(int x, int y) {

	fixed_point_t f = { (((long long) x * FIX_F) / y) };
	return f;
}
