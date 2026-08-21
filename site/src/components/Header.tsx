'use client'

import { Moon, Sun } from 'lucide-react'
import { useTheme } from 'next-themes'
import type { SiteConfig } from '@/config/proofs'

interface HeaderProps {
  config: SiteConfig
}

export function Header({ config }: HeaderProps) {
  const { theme, setTheme } = useTheme()

  return (
    <header className="border-b border-border/50 bg-background/80 backdrop-blur-sm sticky top-0 z-50">
      <div className="max-w-7xl mx-auto px-6 py-4">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-3">
            <Logo />
            <div>
              <h1 className="text-lg font-semibold tracking-tight">{config.name}</h1>
              <p className="text-xs text-muted-foreground">Formal Proofs</p>
            </div>
          </div>

          <div className="flex items-center gap-4">
            <nav className="hidden md:flex items-center gap-5 text-sm">
              <a
                href="https://papers.hanzo.ai"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                Papers
              </a>
              <a
                href={config.website}
                target="_blank"
                rel="noopener noreferrer"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                Website
              </a>
              <a
                href={config.github}
                target="_blank"
                rel="noopener noreferrer"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                GitHub
              </a>
            </nav>
            <button
              onClick={() => setTheme(theme === 'dark' ? 'light' : 'dark')}
              className="p-2 rounded-md text-muted-foreground hover:text-foreground hover:bg-accent transition-colors"
              aria-label="Toggle theme"
            >
              <Sun className="h-4 w-4 hidden dark:block" />
              <Moon className="h-4 w-4 block dark:hidden" />
            </button>
          </div>
        </div>
      </div>
    </header>
  )
}

// The Hanzo mark, same geometry as public/favicon.svg so the header and the
// browser tab show one shape. Source: @hanzo/brand assets/logo/favicon.svg.
function Logo() {
  return (
    <svg
      viewBox="0 0 67 67"
      className="w-7 h-7 text-foreground"
      fill="currentColor"
      role="img"
      aria-label="Hanzo"
      xmlns="http://www.w3.org/2000/svg"
    >
      <path d="M22.21 67V44.6369H0V67H22.21Z" />
      <path d="M66.7038 22.3184H22.2534L0.0878906 44.6367H44.4634L66.7038 22.3184Z" />
      <path d="M22.21 0H0V22.3184H22.21V0Z" />
      <path d="M66.7198 0H44.5098V22.3184H66.7198V0Z" />
      <path d="M66.7198 67V44.6369H44.5098V67H66.7198Z" />
    </svg>
  )
}
