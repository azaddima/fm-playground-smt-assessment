import React from 'react';
import CodeDisplay from './PlainOutput'; 

const App = () => {
  const exampleCode = `print("Hello World")^
  PP = (A+B)(A+C)(B+C)^
  PP = (A+B)(A+C)(B+C)^`;

  return (
    <div>
      <CodeDisplay 
      code={exampleCode} />
    </div>
  );
};

export default App;
