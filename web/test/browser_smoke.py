"""Optional Chromium smoke test for UI layout and interaction.

Runs the real HTML/CSS/JS in Chromium, but uses a synthetic endpoint response.
No Lean executable or network access is required. Requires Python playwright.
"""
from pathlib import Path
from playwright.sync_api import sync_playwright
import json

root = Path(__file__).resolve().parents[1] / 'public'
html = (root / 'index.html').read_text()
html = html.replace('<link rel="stylesheet" href="/style.css">', '')
html = html.replace('<script src="/app.js" type="module"></script>', '')
html = html.replace('</head>', '<style>' + (root / 'style.css').read_text() + '</style></head>')
js = (root / 'app.js').read_text().replace('export function', 'function')
trace = '\n'.join([
    'start|0|0', 'finish|0|0',
    'start|1|INF', 'edge|1|0|2|0|2|INF|2', 'finish|1|2',
    'start|2|INF', 'edge|2|0|5|0|5|INF|5',
    'edge|2|1|3|2|5|5|5', 'finish|2|5',
    'start|3|INF', 'edge|3|1|1|2|3|INF|3',
    'edge|3|2|1|5|6|3|3', 'finish|3|3'
])

with sync_playwright() as p:
    browser = p.chromium.launch(executable_path='/usr/bin/chromium', headless=True, args=['--no-sandbox'])
    page = browser.new_page(viewport={'width': 1440, 'height': 1000})
    errors = []
    page.on('pageerror', lambda error: errors.append(str(error)))
    page.set_content(html)
    page.evaluate('window.fetch=async(url)=>({ok:true,json:async()=>({output:url==="/api/trace"?'
                  + json.dumps(trace) + ':"0: 0\\n1: 2\\n2: 5\\n3: 3"})})')
    page.add_script_tag(content=js)
    assert 'Valid DAG' in page.locator('#parse-status').inner_text()
    assert page.locator('.graph-edge').count() == 5
    page.locator('#run-shortest').click()
    page.wait_for_function('document.querySelector("#trace-counter").textContent.includes("STEP 1")')
    assert page.locator('#trace-next').is_enabled()
    for _ in range(3):
        page.locator('#trace-next').click()
    assert 'Edge 0 → 1' in page.locator('#trace-title').inner_text()
    assert page.locator('.graph-edge.edge-active').count() == 1
    assert page.locator('.graph-node.node-active').count() == 1
    assert page.locator('.graph-node.node-predecessor').count() == 1
    page.screenshot(path=str(root.parent.parent / 'animation-desktop.png'), full_page=True)
    page.locator('#trace-prev').click()
    assert 'initialize' in page.locator('#trace-title').inner_text()
    page.locator('#trace-speed').fill('350')
    page.locator('#trace-play').click()
    page.wait_for_timeout(460)
    assert 'Edge 0 → 1' in page.locator('#trace-title').inner_text()
    page.locator('#trace-play').click()
    page.set_viewport_size({'width': 768, 'height': 900})
    page.screenshot(path=str(root.parent.parent / 'animation-tablet.png'), full_page=True)
    assert page.evaluate('document.documentElement.scrollWidth <= innerWidth')
    page.locator('#graph-text').fill('vertices 2\nsource 0\nedge 1 0 3')
    assert 'expected FROM < TO' in page.locator('#parse-status').inner_text()
    assert page.locator('#trace-next').is_disabled()
    assert not errors, errors
    print('Chromium UI smoke passed: live graph, trace auto-load, stepping, highlighting, timed play, pause, resize, invalidation.')
    browser.close()
