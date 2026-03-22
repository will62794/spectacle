// @ts-check
import { test, expect } from '@playwright/test';

// 
// Runs interpreter tests via playwright by loading the "test" page and checking all statuses are OK.
// 

test('interpreter-tests', async ({ page }) => {
    await page.goto('http://localhost:3000/test.html');
    // await page.goto('http://127.0.0.1:8000/test.html?test=simple5&debug=0');
  
    // Expect a title "to contain" a substring.
    await expect(page.getByText('TLA+ Web Interpreter Tests')).toBeVisible();

    // Wait until all <td class="test-status"> elements contain "Done" in their text.
    await page.waitForFunction(() => {
        const statusCells = Array.from(document.querySelectorAll('td.test-status'));
        return statusCells.length > 0 && statusCells.every(td => td.textContent && td.textContent.includes("Done"));
    });

    // Check until all <td class="test-status"> elements contain "PASS" in their status text. 
    // Otherwise, mark those that have "FAIL" in their status text as failed and fail the test reporting
    // the number of failed tests.
    const failedTests = await page.evaluate(() => {
        const statusCells = Array.from(document.querySelectorAll('td.test-status'));
        return statusCells.filter(td => td.textContent && td.textContent.includes("FAIL")).map(td => td.textContent);
    });
    if (failedTests.length > 0) {
        throw new Error(`Failed tests: ${failedTests.join(', ')}`);
    } else {
        console.log(`All tests passed.`);
    }
  });