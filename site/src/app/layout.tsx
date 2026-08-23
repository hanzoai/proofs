import type { Metadata } from 'next'
import { ThemeProvider } from 'next-themes'
import { siteConfig } from '@/config/proofs'
import './global.css'

export const metadata: Metadata = {
  metadataBase: new URL('https://proofs.hanzo.ai'),
  title: `${siteConfig.name} Formal Proofs`,
  description: siteConfig.description,
  // Both files are the Hanzo mark from @hanzo/brand, copied into public/. The
  // .ico is here because a browser asks for /favicon.ico whether or not a page
  // declares one, and this export has no server to answer that with anything
  // else.
  icons: {
    icon: [
      { url: '/favicon.svg', type: 'image/svg+xml' },
      { url: '/favicon.ico', sizes: '48x48' },
    ],
  },
  openGraph: {
    title: `${siteConfig.name} Formal Proofs`,
    description: siteConfig.description,
    url: 'https://proofs.hanzo.ai',
    siteName: `${siteConfig.name} Proofs`,
    type: 'website',
  },
  twitter: {
    card: 'summary_large_image',
    title: `${siteConfig.name} Formal Proofs`,
    description: siteConfig.description,
  },
}

export default function RootLayout({
  children,
}: {
  children: React.ReactNode
}) {
  // No font loader. Zen ships inside @hanzo/design and global.css declares the
  // faces, so there is no generated family name to bind here.
  return (
    <html lang="en" suppressHydrationWarning>
      <head>
        <script
          dangerouslySetInnerHTML={{
            __html: `(function(){try{var d=document.documentElement;var s=localStorage.getItem('hanzo-proofs-theme');if(s==='dark'||(s!=='light'&&window.matchMedia('(prefers-color-scheme:dark)').matches)){d.classList.add('dark')}else{d.classList.remove('dark')}}catch(e){}})()`,
          }}
        />
      </head>
      <body className="min-h-svh bg-background font-sans antialiased">
        <ThemeProvider
          attribute="class"
          defaultTheme="dark"
          storageKey="hanzo-proofs-theme"
          enableSystem
        >
          {children}
        </ThemeProvider>
      </body>
    </html>
  )
}
