// Root component: demo data for a hypothetical index futures contract "DIX" and the chain.
// Prices are ticks of 0.05; theoretical values were computed offline (Black-76) and are data.
import { assert } from "vreact/spec";
import { type Expiry, validChain } from "./model";
import { OptionsChain } from "./OptionsChain";

/** @opaque */
export const EXPIRIES: readonly Expiry[] = [
  {
    id: 1,
    symbol: "DIX",
    label: "DEC 26",
    future: { bid: 2048, bidQty: 62, ask: 2049, askQty: 56 },
    strikes: [
      { strike: 1920, call: { bid: 146, bidQty: 109, ask: 149, askQty: 117 }, put: { bid: null, bidQty: 0, ask: 19, askQty: 27 }, callTheo: 146, putTheo: 18, vol: 2286 },
      { strike: 1940, call: { bid: 126, bidQty: 38, ask: 129, askQty: 48 }, put: { bid: 23, bidQty: 111, ask: 25, askQty: 105 }, callTheo: 130, putTheo: 22, vol: 2253 },
      { strike: 1960, call: { bid: 112, bidQty: 43, ask: 115, askQty: 20 }, put: { bid: 28, bidQty: 132, ask: 30, askQty: 130 }, callTheo: 115, putTheo: 27, vol: 2221 },
      { strike: 1980, call: { bid: 99, bidQty: 47, ask: 102, askQty: 131 }, put: { bid: 30, bidQty: 119, ask: 32, askQty: 149 }, callTheo: 101, putTheo: 33, vol: 2191 },
      { strike: 2000, call: { bid: 87, bidQty: 22, ask: 90, askQty: 55 }, put: { bid: 39, bidQty: 13, ask: 41, askQty: 45 }, callTheo: 87, putTheo: 39, vol: 2163 },
      { strike: 2020, call: { bid: 73, bidQty: 120, ask: 76, askQty: 45 }, put: { bid: 46, bidQty: 5, ask: 48, askQty: 91 }, callTheo: 75, putTheo: 47, vol: 2136 },
      { strike: 2040, call: { bid: 62, bidQty: 102, ask: 65, askQty: 110 }, put: { bid: 57, bidQty: 126, ask: 59, askQty: 39 }, callTheo: 64, putTheo: 56, vol: 2110 },
      { strike: 2060, call: { bid: 54, bidQty: 69, ask: 56, askQty: 142 }, put: { bid: 61, bidQty: 131, ask: 64, askQty: 48 }, callTheo: 53, putTheo: 65, vol: 2086 },
      { strike: 2080, call: { bid: 41, bidQty: 78, ask: 43, askQty: 8 }, put: { bid: 72, bidQty: 145, ask: 75, askQty: 41 }, callTheo: 44, putTheo: 76, vol: 2063 },
      { strike: 2100, call: { bid: 34, bidQty: 97, ask: 36, askQty: 114 }, put: { bid: 86, bidQty: 126, ask: 89, askQty: 96 }, callTheo: 36, putTheo: 88, vol: 2041 },
      { strike: 2120, call: { bid: 29, bidQty: 18, ask: 31, askQty: 45 }, put: { bid: 97, bidQty: 140, ask: 100, askQty: 151 }, callTheo: 29, putTheo: 101, vol: 2021 },
      { strike: 2140, call: { bid: 21, bidQty: 127, ask: 23, askQty: 38 }, put: { bid: 113, bidQty: 15, ask: 116, askQty: 8 }, callTheo: 23, putTheo: 115, vol: 2002 },
      { strike: 2160, call: { bid: 15, bidQty: 58, ask: 16, askQty: 86 }, put: { bid: 130, bidQty: 68, ask: 133, askQty: 61 }, callTheo: 18, putTheo: 130, vol: 1984 },
      { strike: 2180, call: { bid: null, bidQty: 0, ask: 13, askQty: 67 }, put: { bid: 142, bidQty: 118, ask: 145, askQty: 69 }, callTheo: 14, putTheo: 146, vol: 1967 },
    ],
  },
  {
    id: 2,
    symbol: "DIX",
    label: "MAR 27",
    future: { bid: 2062, bidQty: 84, ask: 2063, askQty: 25 },
    strikes: [
      { strike: 1920, call: { bid: 196, bidQty: 84, ask: 199, askQty: 119 }, put: { bid: 55, bidQty: 77, ask: 57, askQty: 67 }, callTheo: 197, putTheo: 55, vol: 2309 },
      { strike: 1940, call: { bid: 179, bidQty: 6, ask: 182, askQty: 54 }, put: { bid: 59, bidQty: 48, ask: 61, askQty: 153 }, callTheo: 182, putTheo: 60, vol: 2275 },
      { strike: 1960, call: { bid: 168, bidQty: 94, ask: 171, askQty: 19 }, put: { bid: 66, bidQty: 92, ask: 69, askQty: 94 }, callTheo: 168, putTheo: 66, vol: 2242 },
      { strike: 1980, call: { bid: 150, bidQty: 19, ask: 153, askQty: 129 }, put: { bid: 71, bidQty: 74, ask: 74, askQty: 122 }, callTheo: 154, putTheo: 72, vol: 2211 },
      { strike: 2000, call: { bid: 140, bidQty: 135, ask: 143, askQty: 55 }, put: { bid: 75, bidQty: 73, ask: 78, askQty: 15 }, callTheo: 141, putTheo: 79, vol: 2182 },
      { strike: 2020, call: { bid: 129, bidQty: 56, ask: 132, askQty: 111 }, put: { bid: 85, bidQty: 15, ask: 88, askQty: 18 }, callTheo: 129, putTheo: 87, vol: 2154 },
      { strike: 2040, call: { bid: 115, bidQty: 72, ask: 118, askQty: 147 }, put: { bid: 91, bidQty: 147, ask: 94, askQty: 145 }, callTheo: 117, putTheo: 95, vol: 2128 },
      { strike: 2060, call: { bid: 105, bidQty: 98, ask: 108, askQty: 83 }, put: { bid: 102, bidQty: 82, ask: 105, askQty: 39 }, callTheo: 106, putTheo: 104, vol: 2102 },
      { strike: 2080, call: { bid: 93, bidQty: 19, ask: 96, askQty: 54 }, put: { bid: 114, bidQty: 100, ask: 117, askQty: 39 }, callTheo: 96, putTheo: 114, vol: 2079 },
      { strike: 2100, call: { bid: 85, bidQty: 48, ask: 88, askQty: 111 }, put: { bid: 124, bidQty: 43, ask: 127, askQty: 14 }, callTheo: 86, putTheo: 124, vol: 2056 },
      { strike: 2120, call: { bid: 75, bidQty: 120, ask: 78, askQty: 101 }, put: { bid: 132, bidQty: 119, ask: 135, askQty: 145 }, callTheo: 77, putTheo: 135, vol: 2035 },
      { strike: 2140, call: { bid: 64, bidQty: 9, ask: 67, askQty: 41 }, put: { bid: 142, bidQty: 72, ask: 145, askQty: 41 }, callTheo: 68, putTheo: 146, vol: 2015 },
      { strike: 2160, call: { bid: 60, bidQty: 44, ask: 63, askQty: 13 }, put: { bid: 155, bidQty: 56, ask: 158, askQty: 11 }, callTheo: 61, putTheo: 159, vol: 1997 },
      { strike: 2180, call: { bid: 54, bidQty: 6, ask: 56, askQty: 136 }, put: { bid: 167, bidQty: 110, ask: 170, askQty: 34 }, callTheo: 53, putTheo: 171, vol: 1979 },
    ],
  },
  {
    id: 3,
    symbol: "DIX",
    label: "JUN 27",
    future: { bid: 2077, bidQty: 80, ask: 2078, askQty: 38 },
    strikes: [
      { strike: 1920, call: { bid: 235, bidQty: 87, ask: 238, askQty: 69 }, put: { bid: 80, bidQty: 113, ask: 83, askQty: 105 }, callTheo: 238, putTheo: 81, vol: 2334 },
      { strike: 1940, call: { bid: 221, bidQty: 51, ask: 224, askQty: 95 }, put: { bid: 85, bidQty: 142, ask: 88, askQty: 63 }, callTheo: 223, putTheo: 86, vol: 2299 },
      { strike: 1960, call: { bid: 205, bidQty: 15, ask: 208, askQty: 138 }, put: { bid: 90, bidQty: 90, ask: 93, askQty: 139 }, callTheo: 209, putTheo: 92, vol: 2265 },
      { strike: 1980, call: { bid: 196, bidQty: 130, ask: 199, askQty: 134 }, put: { bid: 95, bidQty: 64, ask: 98, askQty: 65 }, callTheo: 196, putTheo: 99, vol: 2233 },
      { strike: 2000, call: { bid: 179, bidQty: 75, ask: 182, askQty: 106 }, put: { bid: 105, bidQty: 131, ask: 108, askQty: 106 }, callTheo: 183, putTheo: 106, vol: 2203 },
      { strike: 2020, call: { bid: 169, bidQty: 8, ask: 172, askQty: 128 }, put: { bid: 111, bidQty: 51, ask: 114, askQty: 29 }, callTheo: 170, putTheo: 113, vol: 2174 },
      { strike: 2040, call: { bid: 154, bidQty: 7, ask: 157, askQty: 32 }, put: { bid: 120, bidQty: 16, ask: 123, askQty: 29 }, callTheo: 158, putTheo: 121, vol: 2147 },
      { strike: 2060, call: { bid: 145, bidQty: 24, ask: 148, askQty: 31 }, put: { bid: 125, bidQty: 26, ask: 128, askQty: 131 }, callTheo: 146, putTheo: 129, vol: 2121 },
      { strike: 2080, call: { bid: 134, bidQty: 57, ask: 137, askQty: 62 }, put: { bid: 137, bidQty: 62, ask: 140, askQty: 98 }, callTheo: 135, putTheo: 138, vol: 2096 },
      { strike: 2100, call: { bid: 125, bidQty: 104, ask: 128, askQty: 66 }, put: { bid: 144, bidQty: 11, ask: 147, askQty: 10 }, callTheo: 125, putTheo: 148, vol: 2073 },
      { strike: 2120, call: { bid: 112, bidQty: 82, ask: 115, askQty: 31 }, put: { bid: 157, bidQty: 108, ask: 160, askQty: 63 }, callTheo: 115, putTheo: 158, vol: 2051 },
      { strike: 2140, call: { bid: 101, bidQty: 46, ask: 104, askQty: 67 }, put: { bid: 167, bidQty: 29, ask: 170, askQty: 101 }, callTheo: 105, putTheo: 168, vol: 2031 },
      { strike: 2160, call: { bid: 96, bidQty: 71, ask: 99, askQty: 136 }, put: { bid: 175, bidQty: 109, ask: 178, askQty: 20 }, callTheo: 96, putTheo: 179, vol: 2011 },
      { strike: 2180, call: { bid: 88, bidQty: 83, ask: 91, askQty: 116 }, put: { bid: 188, bidQty: 92, ask: 191, askQty: 110 }, callTheo: 88, putTheo: 191, vol: 1993 },
    ],
  },
];
// a fact about the constant, proved once by evaluation and then available to every proof
assert(validChain(EXPIRIES));

export function App() {
  return (
    <div className="app">
      <header>
        <h1>Options chain</h1>
        <p className="muted">Hypothetical DIX index futures options · demo data · prices in ticks of 0.05</p>
      </header>
      <OptionsChain expiries={EXPIRIES} />
    </div>
  );
}
