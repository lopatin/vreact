// Entry point (not verified: it only mounts the verified root component).
import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import { SeatsApp } from "./SeatsApp";
import "./styles.css";

createRoot(document.getElementById("root")!).render(
  <StrictMode>
    <SeatsApp />
  </StrictMode>,
);
